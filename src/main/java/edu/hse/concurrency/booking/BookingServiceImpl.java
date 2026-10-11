package edu.hse.concurrency.booking;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

public class BookingServiceImpl implements BookingService {

    private static final Comparator<Seat> SEAT_ORDER = Comparator
            .comparingInt(Seat::row)
            .thenComparingInt(Seat::number);

    private final Hall hall;
    private final Duration holdDuration;

    private final Object cellsMonitor = new Object();
    private final Map<Seat, Cell> cells = new HashMap<>();

    private final Object holdsMonitor = new Object();
    private final Map<Hold, HoldRecord> holds = new IdentityHashMap<>();

    private final Object lifecycleMonitor = new Object();
    private final HashSet<Waiter> waiters = new HashSet<>();

    private final Object expirationMonitor = new Object();
    private final ArrayList<HoldRecord> expiringHolds = new ArrayList<>();

    private final Thread expirationThread;

    private long nextHoldId = 1;
    private volatile boolean stopped;

    public BookingServiceImpl(Hall hall, Duration holdDuration) {
        this.hall = Objects.requireNonNull(hall, "hall");
        this.holdDuration = Objects.requireNonNull(holdDuration, "holdDuration");
        if (holdDuration.isZero() || holdDuration.isNegative()) {
            throw new IllegalArgumentException("holdDuration must be positive");
        }

        expirationThread = new Thread(this::expireHolds, "booking-expiration");
        expirationThread.setDaemon(true);
        expirationThread.start();
    }

    @Override
    public Optional<Hold> hold(String clientId, Set<Seat> seats) {
        List<Cell> requested = validateHoldRequest(clientId, seats);
        ensureRunning();

        return tryCreateHold(clientId, requested);
    }

    @Override
    public Optional<Hold> holdOrWait(String clientId, Set<Seat> seats, Duration timeout)
            throws InterruptedException {
        Objects.requireNonNull(timeout, "timeout");
        List<Cell> requested = validateHoldRequest(clientId, seats);
        if (timeout.isNegative()) {
            throw new IllegalArgumentException("timeout must not be negative");
        }
        ensureRunning();

        if (timeout.isZero()) {
            return tryCreateHold(clientId, requested);
        }

        long timeoutNanos = saturatedNanos(timeout);
        long deadline = saturatedDeadline(timeoutNanos);

        while (true) {
            Waiter waiter = new Waiter();
            AttemptResult attempt = tryCreateHoldOrRegisterWaiter(clientId, requested, waiter);
            if (attempt.hold != null) {
                return Optional.of(attempt.hold);
            }
            if (attempt.sold) {
                return Optional.empty();
            }

            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) {
                unregisterWaiter(waiter, requested);
                return Optional.empty();
            }
            if (attempt.stopped) {
                unregisterWaiter(waiter, requested);
                return Optional.empty();
            }

            try {
                synchronized (waiter) {
                    while (!waiter.signaled) {
                        remaining = deadline - System.nanoTime();
                        if (remaining <= 0) {
                            return Optional.empty();
                        }
                        waiter.wait(remainingMillis(remaining), remainingNanos(remaining));
                    }
                }
            } finally {
                unregisterWaiter(waiter, requested);
            }

            if (stopped) {
                return Optional.empty();
            }
        }
    }

    @Override
    public boolean confirm(Hold hold) {
        Objects.requireNonNull(hold, "hold");
        ensureRunning();

        HoldRecord record = recordByHold(hold);
        if (record == null) {
            return false;
        }

        MutableBoolean confirmed = new MutableBoolean();
        lockCells(record.cells, 0, () -> {
            Instant now = Instant.now();
            if (!record.isEffective(now)) {
                return;
            }
            record.active = false;
            for (Cell cell : record.cells) {
                if (cell.hold == record) {
                    cell.hold = null;
                    cell.sold = true;
                }
            }
            confirmed.value = true;
            signalWaiters(record.cells);
        });

        if (confirmed.value) {
            removeActiveHold(record);
        }
        return confirmed.value;
    }

    @Override
    public boolean release(Hold hold) {
        Objects.requireNonNull(hold, "hold");
        ensureRunning();

        HoldRecord record = recordByHold(hold);
        if (record == null) {
            return false;
        }

        MutableBoolean released = new MutableBoolean();
        lockCells(record.cells, 0, () -> {
            Instant now = Instant.now();
            if (!record.isEffective(now)) {
                return;
            }
            record.active = false;
            for (Cell cell : record.cells) {
                if (cell.hold == record) {
                    cell.hold = null;
                }
            }
            released.value = true;
            signalWaiters(record.cells);
        });

        if (released.value) {
            removeActiveHold(record);
        }
        return released.value;
    }

    @Override
    public SeatStatus status(Seat seat) {
        Objects.requireNonNull(seat, "seat");
        if (!hall.contains(seat)) {
            throw new IllegalArgumentException("seat is outside the hall");
        }

        Cell cell = cellFor(seat);
        synchronized (cell) {
            return cell.status(Instant.now());
        }
    }

    @Override
    public void shutdown() {
        boolean firstShutdown;
        synchronized (lifecycleMonitor) {
            firstShutdown = !stopped;
            stopped = true;
            for (Waiter waiter : waiters) {
                waiter.signal();
            }
        }
        if (!firstShutdown) {
            return;
        }

        synchronized (expirationMonitor) {
            expirationMonitor.notifyAll();
        }

        boolean interrupted = false;
        while (expirationThread.isAlive()) {
            try {
                expirationThread.join();
            } catch (InterruptedException e) {
                interrupted = true;
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }
    }

    private Optional<Hold> tryCreateHold(String clientId, List<Cell> requested) {
        MutableHold result = new MutableHold();
        lockCells(requested, 0, () -> {
            Instant now = Instant.now();
            if (allFree(requested, now)) {
                result.hold = createHoldLocked(clientId, requested, now);
            }
        });
        return Optional.ofNullable(result.hold);
    }

    private AttemptResult tryCreateHoldOrRegisterWaiter(String clientId, List<Cell> requested, Waiter waiter) {
        AttemptResult result = new AttemptResult();
        lockCells(requested, 0, () -> {
            Instant now = Instant.now();
            if (allFree(requested, now)) {
                result.hold = createHoldLocked(clientId, requested, now);
                return;
            }

            result.blockingCells = new ArrayList<>();
            for (Cell cell : requested) {
                if (cell.sold) {
                    result.sold = true;
                    result.blockingCells.clear();
                    return;
                }
                if (cell.isHeld(now)) {
                    result.blockingCells.add(cell);
                }
            }
            result.stopped = !registerWaiterLocked(waiter, result.blockingCells);
        });
        return result;
    }

    private Hold createHoldLocked(String clientId, List<Cell> requested, Instant now) {
        long holdId = nextHoldId();
        Hold hold = new Hold(holdId, clientId, seatsOf(requested), now.plus(holdDuration));
        HoldRecord record = new HoldRecord(hold, new ArrayList<>(requested));
        for (Cell cell : requested) {
            cell.hold = record;
        }
        synchronized (holdsMonitor) {
            holds.put(hold, record);
        }
        synchronized (expirationMonitor) {
            expiringHolds.add(record);
            expirationMonitor.notifyAll();
        }
        return hold;
    }

    private boolean allFree(List<Cell> requested, Instant now) {
        for (Cell cell : requested) {
            if (cell.sold || cell.isHeld(now)) {
                return false;
            }
        }
        return true;
    }

    private boolean registerWaiterLocked(Waiter waiter, List<Cell> blockingCells) {
        synchronized (lifecycleMonitor) {
            if (stopped) {
                return false;
            }
            waiters.add(waiter);
        }
        for (Cell cell : blockingCells) {
            cell.waiters.add(waiter);
        }
        return true;
    }

    private void unregisterWaiter(Waiter waiter, List<Cell> requested) {
        lockCells(requested, 0, () -> {
            for (Cell cell : requested) {
                cell.waiters.remove(waiter);
            }
            synchronized (lifecycleMonitor) {
                waiters.remove(waiter);
            }
        });
    }

    private void signalWaiters(List<Cell> changedCells) {
        HashSet<Waiter> signaled = new HashSet<>();
        for (Cell cell : changedCells) {
            signaled.addAll(cell.waiters);
        }
        for (Waiter waiter : signaled) {
            waiter.signal();
        }
    }

    private long nextHoldId() {
        synchronized (holdsMonitor) {
            return nextHoldId++;
        }
    }

    private void expireHolds() {
        while (true) {
            HoldRecord record = nextExpiredHold();
            if (record == null) {
                return;
            }
            expire(record);
        }
    }

    private HoldRecord nextExpiredHold() {
        synchronized (expirationMonitor) {
            while (true) {
                if (stopped) {
                    return null;
                }

                Instant now = Instant.now();
                HoldRecord nearest = null;
                for (HoldRecord record : expiringHolds) {
                    if (!record.active) {
                        continue;
                    }
                    if (nearest == null || record.hold.expiresAt().isBefore(nearest.hold.expiresAt())) {
                        nearest = record;
                    }
                }

                if (nearest == null) {
                    waitForExpiration(0, 0);
                    continue;
                }

                Duration untilExpiration = Duration.between(now, nearest.hold.expiresAt());
                if (!untilExpiration.isPositive()) {
                    return nearest;
                }
                long nanos = saturatedNanos(untilExpiration);
                waitForExpiration(remainingMillis(nanos), remainingNanos(nanos));
            }
        }
    }

    private void waitForExpiration(long millis, int nanos) {
        try {
            expirationMonitor.wait(millis, nanos);
        } catch (InterruptedException e) {
            // The service never interrupts this thread itself; ignore external interrupts.
        }
    }

    private void expire(HoldRecord record) {
        MutableBoolean expired = new MutableBoolean();
        ArrayList<Cell> changedCells = new ArrayList<>();
        lockCells(record.cells, 0, () -> {
            Instant now = Instant.now();
            if (!record.active || now.isBefore(record.hold.expiresAt())) {
                return;
            }
            record.active = false;
            for (Cell cell : record.cells) {
                if (cell.hold == record) {
                    cell.hold = null;
                    changedCells.add(cell);
                }
            }
            expired.value = true;
            signalWaiters(changedCells);
        });

        if (expired.value) {
            removeActiveHold(record);
        }
    }

    private void removeActiveHold(HoldRecord record) {
        synchronized (holdsMonitor) {
            holds.remove(record.hold);
        }
        synchronized (expirationMonitor) {
            expiringHolds.remove(record);
            expirationMonitor.notifyAll();
        }
    }

    private HoldRecord recordByHold(Hold hold) {
        synchronized (holdsMonitor) {
            return holds.get(hold);
        }
    }

    private List<Cell> validateHoldRequest(String clientId, Set<Seat> seats) {
        Objects.requireNonNull(clientId, "clientId");
        Objects.requireNonNull(seats, "seats");
        if (clientId.isBlank()) {
            throw new IllegalArgumentException("clientId must not be blank");
        }
        if (seats.isEmpty() || seats.size() > MAX_SEATS_PER_HOLD) {
            throw new IllegalArgumentException("hold must contain from 1 to " + MAX_SEATS_PER_HOLD + " seats");
        }

        ArrayList<Seat> sortedSeats = new ArrayList<>(seats.size());
        for (Seat seat : seats) {
            Objects.requireNonNull(seat, "seat");
            if (!hall.contains(seat)) {
                throw new IllegalArgumentException("seat is outside the hall");
            }
            sortedSeats.add(seat);
        }
        sortedSeats.sort(SEAT_ORDER);

        ArrayList<Cell> result = new ArrayList<>(sortedSeats.size());
        for (Seat seat : sortedSeats) {
            result.add(cellFor(seat));
        }
        return result;
    }

    private Cell cellFor(Seat seat) {
        synchronized (cellsMonitor) {
            Cell cell = cells.get(seat);
            if (cell == null) {
                cell = new Cell(seat);
                cells.put(seat, cell);
            }
            return cell;
        }
    }

    private Set<Seat> seatsOf(List<Cell> requested) {
        HashSet<Seat> result = new HashSet<>();
        for (Cell cell : requested) {
            result.add(cell.seat);
        }
        return result;
    }

    private void ensureRunning() {
        if (stopped) {
            throw new IllegalStateException("service is stopped");
        }
    }

    private void lockCells(List<Cell> cells, int index, Runnable action) {
        if (index == cells.size()) {
            action.run();
            return;
        }
        synchronized (cells.get(index)) {
            lockCells(cells, index + 1, action);
        }
    }

    private static long saturatedNanos(Duration duration) {
        try {
            return duration.toNanos();
        } catch (ArithmeticException e) {
            return Long.MAX_VALUE;
        }
    }

    private static long saturatedDeadline(long timeoutNanos) {
        long now = System.nanoTime();
        long deadline = now + timeoutNanos;
        if (deadline < now) {
            return Long.MAX_VALUE;
        }
        return deadline;
    }

    private static long remainingMillis(long nanos) {
        return nanos / 1_000_000L;
    }

    private static int remainingNanos(long nanos) {
        return (int) (nanos % 1_000_000L);
    }

    private static final class Cell {
        private final Seat seat;
        private final HashSet<Waiter> waiters = new HashSet<>();
        private HoldRecord hold;
        private boolean sold;

        private Cell(Seat seat) {
            this.seat = seat;
        }

        private boolean isHeld(Instant now) {
            return hold != null && hold.isEffective(now);
        }

        private SeatStatus status(Instant now) {
            if (sold) {
                return SeatStatus.SOLD;
            }
            if (isHeld(now)) {
                return SeatStatus.HELD;
            }
            return SeatStatus.FREE;
        }
    }

    private static final class HoldRecord {
        private final Hold hold;
        private final List<Cell> cells;
        private volatile boolean active = true;

        private HoldRecord(Hold hold, List<Cell> cells) {
            this.hold = hold;
            this.cells = cells;
        }

        private boolean isEffective(Instant now) {
            return active && now.isBefore(hold.expiresAt());
        }
    }

    private static final class Waiter {
        private boolean signaled;

        private synchronized void signal() {
            signaled = true;
            notify();
        }
    }

    private static final class MutableHold {
        private Hold hold;
    }

    private static final class MutableBoolean {
        private boolean value;
    }

    private static final class AttemptResult {
        private Hold hold;
        private boolean sold;
        private boolean stopped;
        private List<Cell> blockingCells = List.of();
    }
}
