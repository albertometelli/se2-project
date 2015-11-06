module myTaxiService/model

//Auxiliary signatures 
sig Date{} 
sig Time{}

sig Location{ 	
	zone: one Zone, 
}

abstract sig Passenger{} 
sig UnregisteredPassenger extends Passenger{} 
sig RegisteredPassenger extends Passenger{}

abstract sig TaxiState{} 
one sig OutOfService,Emergency extends TaxiState{} 
one sig Available, Busy, Moving extends TaxiState{}

abstract sig Taxi { 	
	driver: lone TaxiDriver, 	
	state: one TaxiState, 	
	numberOfSeats: one Int, 
}  

sig MinivanTaxi extends Taxi {} {numberOfSeats = 9} 
sig NormalTaxi extends Taxi {} {numberOfSeats = 4}

sig TaxiDriver{}

sig Request{ 	
	passenger: one Passenger, 	
	date: one Date, 	
	time: one Time, 	
	numberOfPassengers: one Int, 	
	location: one Location, 
}  {numberOfPassengers>=1}

sig ConfirmedRequest extends Request{ 	
	waitingTime: one Time, 	
	taxis: some Taxi, 
}

sig Reservation{ 	
	passenger: one RegisteredPassenger, 	
	date: one Date, 	
	time: one Time, 	
	numberOfPassengers: one Int, 	
	origin: one Location, 
	destination: one Location,	
	associatedRequest: one Request, 
} {numberOfPassengers>=1 and associatedRequest.passenger = passenger and associatedRequest.location = origin and associatedRequest.numberOfPassengers = numberOfPassengers}

sig Zone{ 	
	requestsPerMinute: one Int, 
}{ requestsPerMinute>0}

//A taxi driver drives one taxi at time 
fact oneTaxiForEachTaxiDriver { 	
	all disj t1, t2 : Taxi | t1.driver != t2.driver 
}

//Non out of service taxis must have a driver 
fact allAvailableTaxiMustHaveADriver { 	
	all t: Taxi | t.state in (Available + Moving + Busy) implies one t.driver 
}

//All busy taxi must have at least a request associated 
fact allBusyTaxiMustHaveAtLeastARequestAssociated { 	
	all t: Taxi | some r: Request | t.state in Busy implies t in r.taxis 
}

//Auxiliary predicate to check if two requests are simultaneous 
pred atTheSameTime[r1,r2 : Request]{ 	
	r1.time = r2.time and r1.date = r2.date 
}

//Each passenger can make at most one request at time 
fact noPassengerMakesMoreThanOneRequestAtTime { 	
	all disj r1,r2 : Request | atTheSameTime[r1,r2] 
		implies r1.passenger != r2.passenger 
}

//Each taxi can carry out at most one request at time 
fact noTaxiCarriesOutMoreThanOneRequestAtTime { 	
	all disj r1, r2: ConfirmedRequest | atTheSameTime[r1,r2] 
		implies r1.taxis != r2.taxis 
}

//Each request can be associated to at most one reservation 
fact eachRequestAssociatedToAtMostOneReservation { 	
	all r: Request | lone re: Reservation | 
		re.associatedRequest = r 
}

//Origin and destination for each request must be different
fact originAndDestinationDifferent {
	all r: Reservation | r.origin != r.destination
}

//In each request the number of seats must be sufficient wrt number of passengers
fact numberOfSeatsSufficient { 	
	all r: ConfirmedRequest | sum r.taxis.numberOfSeats 
		>= r.numberOfPassengers 
}

/* 
This is syntactically and semantically correct but it is writter in second order logic so it cannot be executed 
fact numberOfSeatsAreTheMinimumRequired { 	
	all r: ConfirmedRequest | no taxiSubset: set Taxi | taxiSubset in r.taxis and taxiSubset != r.taxis and 		sum taxiSubset.numberOfSeats >= r.numberOfPassengers 
}
*/

//The same fact rephrased in FOL: the number of taxis sent are the minimun requested to pick up all passengers 
fact numberOfSeatsAreTheMinimumRequired { 	
	all r: ConfirmedRequest | no t: Taxi | t in r.taxis and sum r.taxis.numberOfSeats - t.numberOfSeats >= r.numberOfPassengers 
}

//Returns the number of in service taxis
fun numberOfInServiceTaxis: Int { 	
	#state.Available + #state.Busy + #state.Moving
}

//At least 20% of total number of taxis must be in service
fact atLeast20PerCentOfTaxisAreNotOutOfService { 	
	mul[numberOfInServiceTaxis[],2] >= #Taxi 
}

//Just builds a world satisfying constraints
pred show{}

//run show for 4 but 5 Int, exactly 1 Zone, exactly 1 Reservation, exactly 2 Request,  exactly 1 ConfirmedRequest, exactly 1 NormalTaxi, exactly 1 MinivanTaxi, exactly 2 Location, exactly 1 Date, exactly 1 Time, exactly 1 RegisteredPassenger, exactly 1 UnregisteredPassenger

//Predicate for sending a request: if the request is not already confirmed and it is not already in the set it is added to the set 
pred sendRequest[setOfRequests,setOfRequests': set Request, request: Request] { 	
	no ((ConfirmedRequest + setOfRequests) & request)  implies  		
		setOfRequests' = setOfRequests + request 
	else
		setOfRequests' = setOfRequests 
}

//run sendRequest for 10 but 5 Int, 1 Zone, 0 Reservation, exactly 4 Request,  1 ConfirmedRequest, 2 Passenger, 3 Taxi

//Predicate for sending a reservation: if the reservation is not already in the set it is added  to the set and a corresponding request is generated 
pred sendReservation[setOfReservations,setOfReservations': set Reservation, reservation: Reservation] { 	
	no (setOfReservations & reservation) implies (
		setOfReservations' = setOfReservations + reservation and  		
		one request: Request | reservation.associatedRequest = request )
	else
		setOfReservations' = setOfReservations 
}

//run sendReservation for 10 but 5 Int, 1 Zone, exactly 3 Reservation, 3 Request, 3 Passenger, 3 Taxi, exactly 3 Location, exactly 3 TaxiDriver, exactly 1 Time, exactly 1 Date

//Predicate for deleting a reservation: if reservation is present it is removed and the corresponding request no longer exists 
pred cancelReservation[setOfReservations,setOfReservations': set Reservation, reservation: Reservation]{
	one setOfReservations & reservation implies
		setOfReservations' = setOfReservations - reservation
	else
		setOfReservations' = setOfReservations
}

//run cancelReservation for 10 but 5 Int, 1 Zone, exactly 2 Reservation, 2 Request, 2 Passenger, 3 Taxi, exactly 1 TaxiDriver, exactly 1 Date, exactly 1 Time, exactly 2 Location

//Verifies whether at least one taxi is in service 
assert ifOneTaxiExistsItIsInService { 	
	one Taxi implies Taxi.state in (Available + Busy + Moving) 
}

//check ifOneTaxiExistsItIsInService for 10

//Verifies if number of seats is the minimun necessary
assert numberOfSeatsAreTheMinimunNecessary {
	all r: ConfirmedRequest | r.numberOfPassengers <= sum r.taxis.numberOfSeats and r.numberOfPassengers <= plus[sum r.taxis.numberOfSeats ,MinivanTaxi.numberOfPassengers]
}

//check numberOfSeatsAreTheMinimunNecessary for 10

//Request carried out by the same taxi driver must be different in date or time
assert allRequestOfTheSameTaxiDriverDifferentInTime {
	all td: TaxiDriver | all disj r1,r2: ConfirmedRequest | td in (r1.taxis.driver & r2.taxis.driver) implies not atTheSameTime[r1,r2]
}

//check allRequestOfTheSameTaxiDriverDifferentInTime for 10

//Each reservation has a request associated with the same origin
assert eachReservationHasARequestWithSameOrigin {
	all r: Reservation | some re: Request | r.origin = re.location
}

//check eachReservationHasARequestWithSameOrigin for 10





