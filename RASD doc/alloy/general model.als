module myTaxiService/model

//Auxiliary signatures 
sig Date{} 
sig Time{}

sig Location{ 	
zone: lone Zone, 
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
	location: one Location, 	
	associatedRequest: one Request, 
} 
{numberOfPassengers>=1 and associatedRequest.passenger = passenger}

sig Zone{ 	
	adjacentZones: some Zone, 	
	requestsPerMinute: one Int, 
}{ requestsPerMinute>0}

//A taxi driver drives one taxi at time 
fact oneTaxiForEachTaxiDriver { 	
	all disj t1, t2 : Taxi | t1.driver != t2.driver 
}

//Available taxis must have a driver 
fact allAvailableTaxiMustHaveADriver { 	
	all t: Taxi | t.state in Available implies one t.driver 
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

//In each request the number of seats must be sufficient wrt number of passengers
fact numberOfSeatsSufficient { 	
	all r: ConfirmedRequest | sum r.taxis.numberOfSeats 
		>= r.numberOfPassengers 
}

//Returns the number of in service taxis
fun numberOfInServiceTaxis: Int { 	
	#state.Available + #state.Busy + #state.Moving
}

//At least 50% of total number of taxis must be available
fact atLeast50PerCentOfTaxisAreNotOutOfService { 	
	mul[numberOfInServiceTaxis[],2] >= #Taxi 
}

//Just builds a world satisfying constraints
pred show{}

//run show for 4 but 5 Int, exactly 1 Zone, exactly 1 Reservation, exactly 3 Request

//Predicate for sending a request: if the request is not already confirmed and it is not already in the set it is added to the set 
pred sendRequest[setOfRequests,setOfRequests': set Request, request: Request] { 	
	no ((ConfirmedRequest + setOfRequests) & request)  implies  		
		setOfRequests' = setOfRequests + request 
}

//run sendRequest for 10 but 5 Int, 0 Zone, 0 Reservation, 6 Request,  2 ConfirmedRequest, 2 Passenger, 3 Taxi

//Predicate for sending a reservation: if the reservation is not already in the set it is added  to the set and a corresponding request is generated 
pred sendReservation[setOfReservations,setOfReservations': set Reservation, reservation: Reservation] { 	
	no (setOfReservations & reservation) implies
		setOfReservations' = setOfReservations + reservation and  		
		one request: Request | reservation.associatedRequest = request 
}

//run sendReservation for 10 but 5 Int, 0 Zone, 4 Reservation, 3 Request, 2 Passenger, 3 Taxi

//Predicate for deleting a reservation: if reservation is present it is removed and the corresponding request no longer exists 
pred cancelReservation[setOfReservations,setOfReservations': set Reservation, reservation: Reservation]{
	one setOfReservations & reservation implies
		setOfReservations' = setOfReservations - reservation and
		no request: Request | reservation.associatedRequest = request  
}

//run cancelReservation for 10 but 5 Int, 0 Zone, 4 Reservation, 3 Request, 2 Passenger, 3 Taxi

//Verifies whether at least one taxi is in service 
assert ifOneTaxiExistsItIsInService { 	
	one Taxi implies Taxi.state in (Available + Busy + Moving) 
}

check ifOneTaxiExistsItIsInService
