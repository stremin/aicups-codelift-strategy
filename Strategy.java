package core;

import core.API.Elevator;
import core.API.Passenger;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class Strategy extends BaseStrategy {
    private static final int ELEVATOR_WAITING = 0;
    private static final int ELEVATOR_MOVING = 1;
    private static final int ELEVATOR_OPENING = 2;
    private static final int ELEVATOR_FILLING = 3;
    private static final int ELEVATOR_CLOSING = 4;

    private static final int PASSENGER_WAITING_FOR_ELEVATOR = 1;
    private static final int PASSENGER_MOVING_TO_ELEVATOR = 2;
    private static final int PASSENGER_RETURNING = 3;
    private static final int PASSENGER_MOVING_TO_FLOOR = 4;
    private static final int PASSENGER_USING_ELEVATOR = 5;
    private static final int PASSENGER_EXITING = 6;

    private static final int MAX_PASSENGERS = 20;
    private static final int TICKS_TO_EXIT = 40;
    private static final int TICKS_TO_CALL_ENEMY = 40;
    private static final int TICKS_TO_STAY_OPEN = 40;
    private static final int WALKING_TIME = 500;
    private static final int TIME_TO_AWAY = 500;
    private static final int DOORS_TIME = 100;
    private static final int TICKS_PER_FLOOR = 50;
    private static final int HORIZONTAL_SPEED = 2;
    private static final int FIRST_ELEVATOR_POSITION = 60;
    private static final int ELEVATOR_OFFSET = 80;
    private static final int MAX_TIME = 7200; // not documented?

    private final Random random = new Random(123);

    private String playerType;
    private int tick = 0;

    private List<ExpectedPassenger> expectedPassengers = new ArrayList<>();
    private Set<Integer> lastPassengers = new LinkedHashSet<>();
    private Set<Integer> notMovingToFloorPassengers = new LinkedHashSet<>(); // not moving_to_floor
    private Set<Integer> waitingElevators = new LinkedHashSet<>();
    private Map<Integer, PassengerRoute> passengerRoutes = new LinkedHashMap<>(); // passengerId -> route

    public void onTick(List<Passenger> myPassengers, List<Elevator> myElevators, List<Passenger> enemyPassengers, List<Elevator> enemyElevators) {
        tick++;

        log("tick: " + tick);

        if(tick == 1) {
            init(myElevators, enemyElevators);
        }

        final List<Passenger> passengers = new ArrayList<>();
        passengers.addAll(myPassengers);
        passengers.addAll(enemyPassengers);

        final List<Elevator> elevators = new ArrayList<>();
        elevators.addAll(myElevators);
        elevators.addAll(enemyElevators);

        calcExpectedPassengers(passengers, elevators);

        final Map<Integer, List<Passenger>> passengersByFloor = new HashMap<>();
        for (Passenger passenger : passengers) {
            if(passenger.getState() < PASSENGER_MOVING_TO_FLOOR) {
                passengersByFloor.putIfAbsent(passenger.getFloor(), new ArrayList<>());
                passengersByFloor.get(passenger.getFloor()).add(passenger);
            }
        }

        for (Elevator elevator : myElevators) {
            final List<Passenger> passengersAtThisFloor = passengersByFloor.getOrDefault(elevator.getFloor(), Collections.emptyList());
            switch (elevator.getState()) {
                case ELEVATOR_WAITING: {
                    chooseNextFloor(elevator, passengersByFloor, elevators);
                    break;
                }
                case ELEVATOR_FILLING: {
                    List<Passenger> passengersForElevator = new ArrayList<>(passengersAtThisFloor);

                    if(elevator.getFloor() == 1 && tick < 2000) {
                        // start of the game - take only valuable passengers
                        passengersForElevator = passengersAtThisFloor.stream()
                                .filter(passenger -> passenger.getDestFloor() >= 5 ||
                                        ((elevator.getId() == 7 || elevator.getId() == 8) && passenger.getDestFloor() == 4))
                                .collect(Collectors.toList());

                        if(elevator.getId() == 1 || elevator.getId() == 2) {
                            passengersForElevator = passengersAtThisFloor.stream()
                                    .filter(passenger -> passenger.getDestFloor() >= 8)
                                    .collect(Collectors.toList());
                        }
                        if(elevator.getId() == 3 || elevator.getId() == 4) {
                            passengersForElevator = passengersAtThisFloor.stream()
                                    .filter(passenger -> passenger.getDestFloor() >= 7)
                                    .collect(Collectors.toList());
                        }

                        if (elevator.getPassengers().stream().filter(passenger -> !passenger.getDestFloor().equals(elevator.getFloor())).count() >= MAX_PASSENGERS) {
                            chooseNextFloor(elevator, passengersByFloor, elevators);
                        } else {
                            assignPassengers(elevator, passengersForElevator);
                        }
                        break;
                    }

                    if (elevator.getPassengers().stream().filter(passenger -> !passenger.getDestFloor().equals(elevator.getFloor())).count() >= MAX_PASSENGERS) {
                        chooseNextFloor(elevator, passengersByFloor, elevators);
                    } else {
                        final List<Elevator> badAnyElevators = elevators.stream()
                                .filter(elevator1 -> !elevator1.getId().equals(elevator.getId()) &&
                                        elevator1.getFloor().equals(elevator.getFloor()) &&
                                        elevator1.getState() == ELEVATOR_FILLING &&
                                        elevator1.getPassengers().size() < MAX_PASSENGERS &&
                                        elevatorDistanceFromCenter(elevator1.getId()) < elevatorDistanceFromCenter(elevator.getId()))
                                .collect(Collectors.toList());
                        final List<ExpectedPassenger> expectedPassengers2 = expectedPassengers.stream()
                                .filter(expected -> expected.floor == elevator.getFloor())
                                .filter(expected -> expected.tick < tick + 200)
                                .collect(Collectors.toList());
                        boolean canCollectExpected = expectedPassengers2.size() > 0 && badAnyElevators.isEmpty();
                        double expectedValue = expectedPassengers2.stream().mapToDouble(this::expectedPassengerValue2).sum();
                        final int expectedValueLimit = 150;

                        if (passengersAtThisFloor.stream().mapToDouble(this::passengerValue).sum() < 100 && (!canCollectExpected || expectedValue < expectedValueLimit)) {
                            chooseNextFloor(elevator, passengersByFloor, elevators);
                        } else {
                            final List<Passenger> exitingPassengers = getExitingPassengers(elevator, elevator.getFloor());
                            final List<Passenger> enteringPassengers = passengersAtThisFloor.stream()
                                    .filter(passenger -> passenger.getElevator() != null && passenger.getElevator().equals(elevator.getId()))
                                    .collect(Collectors.toList());
                            final int freePlaces = Math.max(0, MAX_PASSENGERS - (elevator.getPassengers().size() - exitingPassengers.size()) - enteringPassengers.size());
                            passengersForElevator = passengersForElevator.stream()
                                    .filter(passenger -> canCall_incorrect(elevator, passenger, elevators))
                                    .sorted(Comparator.comparing(passenger -> -passengerValue(passenger)))
                                    .limit(freePlaces)
                                    .collect(Collectors.toList());
                            if(enteringPassengers.isEmpty() && passengersForElevator.isEmpty() && (!canCollectExpected || expectedValue < expectedValueLimit)) {
                                chooseNextFloor(elevator, passengersByFloor, elevators);
                            } else {
                                if(!passengersForElevator.isEmpty()) {
                                    log("assign e" + elevator.getId() + ": " + passengersForElevator.stream().map(this::passengerToString).collect(Collectors.toList()));
                                    assignPassengers(elevator, passengersForElevator);
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }

    private String passengerToString(Passenger passenger) {
        return  passenger.getType().substring(0, 1) + passenger.getId() + ">" + passenger.getDestFloor() +
                (passenger.getElevator() != null ? "e" + passenger.getElevator() : "");
    }

    private boolean canCall_incorrect(Elevator elevator, Passenger passenger, List<Elevator> elevators) {
        if(elevator.getId().equals(passenger.getElevator())) {
            return false; // already called
        }
        switch (passenger.getState()) {
            case PASSENGER_WAITING_FOR_ELEVATOR:
                return true;
            case PASSENGER_MOVING_TO_ELEVATOR: {
                final Elevator elevator2 = elevators.stream().filter(elevator1 -> elevator1.getId().equals(passenger.getElevator())).findFirst().get();
                if (elevator2.getType().equals(playerType)) {
                    return false; // already going to our elevator
                } else {
                    final int closestEnemyElevatorX = elevators.stream()
                            .filter(elevator1 -> !elevator1.getType().equals(playerType))
                            .filter(elevator1 -> elevator1.getState() != ELEVATOR_MOVING && elevator1.getFloor().equals(elevator.getFloor()))
                            .min(Comparator.comparingInt(elevator1 -> getElevatorX(elevator)))
                            .map(this::getElevatorX)
                            .orElse(Integer.MAX_VALUE);
                    if ((passenger.getType().equals(playerType) || elevator.getTimeOnFloor() > DOORS_TIME + TICKS_TO_CALL_ENEMY) &&
                            Math.abs(passenger.getX() - getElevatorX(elevator)) < Math.abs(passenger.getX() - closestEnemyElevatorX)) {
                        return true; // can change call
                    }
                    return false;
                }
            }
            case PASSENGER_RETURNING:
                return true;
        }
        return false;
    }

    private int getElevatorX(Elevator elevator) {
        return Arrays.asList(-60, 60, -60 - 80, 60 + 80, -60 - 80 - 80, 60 + 80 + 80, -60 - 80 - 80 - 80, 60 + 80 + 80 + 80).get(elevator.getId() - 1);
    }

    private void calcFirstExpectedPassengers(String myType, String enemyType) {
        int count = 0;
        for(int i = 1; i < 2000; i += 20) {
            expectPassenger(new ExpectedPassenger(count * 2 + (myType.equals("FIRST_PLAYER") ? 1 : 2), myType, 1, i, "init"));
            expectPassenger(new ExpectedPassenger(count * 2 + (enemyType.equals("FIRST_PLAYER") ? 1 : 2), enemyType, 1, i, "init"));
            passengerRoutes.put(count * 2 + 1, new PassengerRoute());
            passengerRoutes.put(count * 2 + 2, new PassengerRoute());
            count++;
        }
    }

    private void calcExpectedPassengers(List<Passenger> passengers, List<Elevator> elevators) {
        elevators.forEach(elevator -> {
            if(waitingElevators.contains(elevator.getId())) {
                elevator.getPassengers().stream()
                        .filter(passenger -> passenger.getDestFloor().equals(elevator.getNextFloor()))
                        .forEach(passenger -> {
                            passengerRoutes.get(passenger.getId()).visited++;
                            if(passenger.getDestFloor() != 1) {
                                ExpectedPassenger expected = new ExpectedPassenger(passenger.getId(), elevator.getType(), elevator.getNextFloor(),
                                        tick + ticksToFloor(elevator, elevator.getNextFloor()) + DOORS_TIME + TICKS_TO_EXIT + WALKING_TIME + 1,
                                        "exit");
                                expectPassenger(expected);
                            }
                        });
            }
        });

        passengers.stream()
                .filter(passenger -> notMovingToFloorPassengers.contains(passenger.getId()) && passenger.getState() == PASSENGER_MOVING_TO_FLOOR)
                .forEach(passenger -> {
                    passengerRoutes.get(passenger.getId()).visited++;
                    if(passenger.getDestFloor() != 1) {
                        int ticksToDest = (passenger.getDestFloor() > passenger.getFromFloor() ? 200 : 100) * Math.abs(passenger.getDestFloor() - passenger.getFromFloor());
                        expectPassenger(new ExpectedPassenger(passenger.getId(), passenger.getType(), passenger.getDestFloor(), tick + ticksToDest + WALKING_TIME + 1, "stair"));
                    }
                });
        for (Passenger passenger : passengers) {
            if(!lastPassengers.contains(passenger.getId())) {
                // new passenger
                final Optional<ExpectedPassenger> found = expectedPassengers.stream()
                        .filter(expected -> expected.tick == tick &&
                                expected.id == passenger.getId() &&
                                expected.type.equals(passenger.getType()) && expected.floor == passenger.getFloor())
                        .findFirst();
                if(found.isPresent()) {
                    expectedPassengers.remove(found.get());
                }
                passengerRoutes.get(passenger.getId()).destinations.add(passenger.getDestFloor());
            }
        }
        expectedPassengers = expectedPassengers.stream().filter(expectedPassenger -> expectedPassenger.tick > tick - 5).collect(Collectors.toList());
        lastPassengers = passengers.stream().map(Passenger::getId).collect(Collectors.toSet());
        notMovingToFloorPassengers = passengers.stream()
                .filter(passenger -> passenger.getState() != PASSENGER_MOVING_TO_FLOOR)
                .map(Passenger::getId)
                .collect(Collectors.toSet());
        waitingElevators = elevators.stream()
                .filter(elevator -> elevator.getState() == ELEVATOR_WAITING)
                .map(Elevator::getId)
                .collect(Collectors.toSet());
    }

    private Integer nextFloor(Integer passengerId) {
        PassengerRoute route = passengerRoutes.get(passengerId);
        if(route.visited == 5) {
            return 1;
        }
        PassengerRoute route2 = passengerRoutes.get(passengerId % 2 == 1 ? passengerId + 1 : passengerId - 1);
        List<Integer> path = route.destinations.size() > route2.destinations.size() ? route.destinations : route2.destinations;
        return route.visited < path.size() ? path.get(route.visited) : null;
    }

    private void expectPassenger(ExpectedPassenger expectedPassenger) {
        expectedPassengers.add(expectedPassenger);
    }

    private void assignPassengers(Elevator elevator, List<Passenger> passengers) {
        for (Passenger passenger : passengers) {
            assignToElevator(elevator, passenger);
        }
    }

    private void assignToElevator(Elevator elevator, Passenger passenger) {
        passenger.setElevator(elevator);
    }

    private void init(List<Elevator> myElevators, List<Elevator> enemyElevators) {
        playerType = myElevators.get(0).getType();
        calcFirstExpectedPassengers(myElevators.get(0).getType(), enemyElevators.get(0).getType());
    }

    private void chooseNextFloor(Elevator elevator, Map<Integer, List<Passenger>> passengersByFloor, List<Elevator> elevators) {
        if(elevator.getTimeOnFloor() < DOORS_TIME + TICKS_TO_STAY_OPEN) {
            return;
        }
        // it's only possible to change destination while elevator is not moving
        // after CLOSING state there is one tick of WAITING state, and then - MOVING
        // so after closing doors we reevaluate targets once again (side effect, but good)
        if(elevator.getState() == ELEVATOR_FILLING) {
            // fake destination, real destination will be set in WAITING state
            goToFloor(elevator, random.nextInt(9) + 1);
            return;
        }
        Integer bestFloor = IntStream.rangeClosed(1, 9)
                .filter(floor -> floor != elevator.getFloor())
                .boxed()
                .max(Comparator.comparingDouble(floor -> evaluateFloor(elevator, floor, passengersByFloor, elevators, tick)))
                .get();
        goToFloor(elevator, bestFloor);
    }

    private double evaluateFloor(Elevator elevator, int floor, Map<Integer, List<Passenger>> passengersByFloor, List<Elevator> elevators, int tick) {
        final int waitOnFloor = Math.max(0, (TICKS_TO_STAY_OPEN - elevator.getTimeOnFloor()));
        int arriveAt = tick + waitOnFloor + (elevator.getState() == ELEVATOR_FILLING ? DOORS_TIME : 0) + ticksToFloor(elevator, floor) + DOORS_TIME;
        if(arriveAt >= MAX_TIME - 10) {
            return 0;
        }

        final List<ArrivingElevator> arrivingElevators = elevators.stream()
                .filter(elevator1 -> !elevator1.getId().equals(elevator.getId()))
                .filter(elevator1 -> (elevator1.getFloor() == floor &&
                        (elevator1.getState() == ELEVATOR_OPENING || elevator1.getState() == ELEVATOR_FILLING)) ||
                        elevator1.getState() == ELEVATOR_MOVING && elevator1.getNextFloor() == floor)
                .map(elevator1 -> new ArrivingElevator(elevator1,
                        elevator1.getState() == ELEVATOR_MOVING ? tick + ticksToFloor(elevator1, floor) + DOORS_TIME :
                                tick - elevator1.getTimeOnFloor() + DOORS_TIME,
                        MAX_PASSENGERS - (int) elevator1.getPassengers().stream().filter(passenger -> passenger.getDestFloor() == floor).count()))
                .filter(arrivingElevator -> arrivingElevator.arriveAt < MAX_TIME)
                .collect(Collectors.toList());

        final List<Passenger> exitingPassengers = getExitingPassengers(elevator, floor);
        final List<ExpectedPassenger> passengers =
                Stream.concat(
                        passengersByFloor.getOrDefault(floor, Collections.emptyList()).stream()
                                .filter(passenger -> tick + passenger.getTimeToAway() > arriveAt + 100)
                                .map(passenger -> new ExpectedPassenger(passenger.getId(), passenger.getType(), floor, tick, " ")),
                        expectedPassengers.stream()
                                .filter(expected -> expected.floor == floor && expected.tick < arriveAt + 100 && expected.tick + TIME_TO_AWAY > arriveAt + 100))
                        .filter(expected -> arriveAt + Math.max(elevatorDistanceFromCenter(elevator.getId()) / HORIZONTAL_SPEED, TICKS_TO_STAY_OPEN) +
                                DOORS_TIME + Math.abs(expected.floor - floor) * TICKS_PER_FLOOR * 1.2 /* 1.2 - eval weight*/ + DOORS_TIME < MAX_TIME - 10)
                        .filter(expected -> arrivingElevators.stream()
                                    .filter(arrivingElevator -> arrivingElevator.arriveAt < arriveAt && expected.tick < arriveAt)
                                .count() == 0)
                        .filter(expected -> arrivingElevators.stream()
                                    .filter(arrivingElevator -> arrivingElevator.arriveAt >= arriveAt && arrivingElevator.arriveAt < expected.tick &&
                                            elevatorDistanceFromCenter(arrivingElevator.elevator.getId()) < elevatorDistanceFromCenter(elevator.getId()))
                                .count() == 0)
                        .collect(Collectors.toList());
        final double outsideValue = passengers.stream()
                .mapToDouble(this::expectedPassengerValue2)
                .sum();

        final int freePlaces = MAX_PASSENGERS - (elevator.getPassengers().size() - exitingPassengers.size());
        final double correctedOutsideValue = passengers.stream()
                .map(this::expectedPassengerValue2)
                .sorted(Comparator.reverseOrder())
                .mapToDouble(Double::doubleValue)
                .limit(freePlaces)
                .sum();
        final double insideValue = exitingPassengers.stream().mapToDouble(this::passengerValue).sum();
        final double result = (correctedOutsideValue + insideValue * 2) * (1 - Math.abs(floor - elevator.getFloor()) * 0.07);
        log("evFl e" + elevator.getId() + ">" + floor +
                " o" + passengers.size() + "!" + (int) outsideValue + "!" + (int) correctedOutsideValue +
                " i" + exitingPassengers.size() + "!" + (int) insideValue +
                " r" + (int) result +
                " ar" + arriveAt);
        return result;
    }

    private int elevatorDistanceFromCenter(int elevatorId) {
        return FIRST_ELEVATOR_POSITION + (elevatorId - 1) / 2 * ELEVATOR_OFFSET;
    }

    private double expectedPassengerValue2(ExpectedPassenger expected) {
        final Integer destFloor = nextFloor(expected.id);
        return expectedPassengerValue(expected,
                destFloor != null ?
                        Math.abs(destFloor - expected.floor) :
                        firstFloorProbability(expected.id) * (expected.floor - 1) + (1 - firstFloorProbability(expected.id)) * averageTravel(expected.floor));
    }

    private int ticksToFloor(Elevator elevator, int floor) {
        if(elevator.getFloor() > floor) {
            return (int) Math.ceil(TICKS_PER_FLOOR * (elevator.getY() - floor));
        }
        double ticksPerFloor = TICKS_PER_FLOOR;
        for (Passenger passenger : elevator.getPassengers()) {
            ticksPerFloor *= passenger.getWeight();
        }
        if(elevator.getPassengers().size() > 10) {
            ticksPerFloor *= 1.1;
        }
        return (int) (ticksPerFloor * (floor - elevator.getY()));
    }

    private List<Passenger> getExitingPassengers(Elevator elevator, int floor) {
        return elevator.getPassengers().stream()
                    .filter(passenger -> passenger.getDestFloor().equals(floor))
                    .collect(Collectors.toList());
    }

    private void goToFloor(Elevator elevator, int nextFloor) {
        elevator.goToFloor(nextFloor);
    }

    private int passengerValue(Passenger passenger) {
        return (passenger.getType().equals(playerType) ? 10 : 20) * Math.abs(passenger.getDestFloor() - passenger.getFromFloor());
    }

    private double expectedPassengerValue(ExpectedPassenger passenger, double travel) {
        return (passenger.type.equals(playerType) ? 10 : 20) * travel;
    }

    private double averageTravel(int floor) {
        return IntStream.rangeClosed(2, 9)
                .filter(destFloor -> destFloor != floor)
                .map(destFloor -> Math.abs(destFloor - floor))
                .sum() / 9.0; // should be /7 but it works a bit worse
    }

    private double firstFloorProbability(int passengerId) {
        final PassengerRoute route = passengerRoutes.get(passengerId);
        return route == null ? 0 : 1.0 / (6 - route.visited);
    }

    private static class ExpectedPassenger {
        final int id;
        final String type;
        final int floor;
        final int tick;
        final String kind;

        ExpectedPassenger(int id, String type, int floor, int tick, String kind) {
            this.id = id;
            this.type = type;
            this.floor = floor;
            this.tick = tick;
            this.kind = kind;
        }

        @Override
        public String toString() {
            return "id=" + id + ", t=" + tick + ", f=" + floor + ", t=" + type.substring(0, 1) + ", k=" + kind.substring(0, 1);
        }
    }

    private static class PassengerRoute {
        final List<Integer> destinations = new ArrayList<>();
        int visited;
    }

    private static class ArrivingElevator {
        final Elevator elevator;
        final int arriveAt;
        final int freePlaces;

        ArrivingElevator(Elevator elevator, int arriveAt, int freePlaces) {
            this.elevator = elevator;
            this.arriveAt = arriveAt;
            this.freePlaces = freePlaces;
        }
    }
}
