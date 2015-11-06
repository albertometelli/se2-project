module myTaxiService/queue

abstract sig TaxiState{} 
one sig OutOfService,Emergency extends TaxiState{} 
one sig Available, Busy, Moving extends TaxiState{}

sig Taxi { 	
	state: one TaxiState, 
}

sig Zone{ 	
	queue: one Queue, 	
	adjacentZones: some Zone, 
}

//Queue definition
sig Queue { 	
	root: lone Node 
}

sig Node { 	
	taxi: one Taxi, 	
	next: lone Node 
}

//Structural properties 
fact queueStructuralProperties { 
	
	//Each node belongs to exactly one queue 	
	all n: Node | one q: Queue | n in q.root.*next	

	//No cycles
	no n: Node | n in n.^next									 
}

//Each queue must belong to exactly one zone 
fact eachQueueBelongsToExactlyOneZone { 	
	all q: Queue | one z: Zone | q in z.queue 
}

//Adjacency relation between zones is simmetric but not reflexive 
fact adjacencySimmetricButNotReflexive 
{ 	
	adjacentZones in ~adjacentZones 	
	no adjacentZones & iden 
}

//Returns the set of taxis belonging to the queue q 
fun getTaxisFromQueue[q: Queue] : set Taxi {
	q.root.*next.taxi 
}

//Queues must store only available taxis 
fact allTaxisInQueueAreAvailable { 	
	all q: Queue | getTaxisFromQueue[q].state in Available 
}

//Each available taxi belongs to exactly one node  
	fact eachTaxiBelongsToExactlyOneNode { 	
	all t: Taxi | t.state in Available implies (one n: Node | n.taxi = t) 
} 

//Builds a realistic world 	
pred showQueues{ 	
	some q: Queue | #getTaxisFromQueue[q]>3 	
	some t: Taxi | t.state in OutOfService 	
	some t: Taxi | t.state in Busy 
}

run showQueues for 10 but exactly 4 Zone, exactly 10 Taxi

//No available taxi are not present any queue 
assert noAvailableTaxiNotInQueue { 	
	no t: Taxi | t.state in Available and (no q:Queue | t in getTaxisFromQueue[q]) 
}

//check noAvailableTaxiNotInQueue for 10

//There are no taxi that appear in more than one queue
assert noTaxiSharedBetweenQueus { 	
	all disj q1,q2: Queue | no getTaxisFromQueue[q1] &  getTaxisFromQueue[q2]  
} 

check noTaxiSharedBetweenQueus for 10
