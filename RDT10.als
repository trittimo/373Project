module RDT10
open util/ordering[State]

// Data which can be sent across the network
// The contents of the data doesn't actually matter
// Synonymous in this case with a packet
sig Data {}

// A reliable channel to send data across
sig Channel {
	// The data we intend to send
	data : set Data
}

// Used to represent a sender or a receiver
sig User {
	buffer : set Data
}

// Used to represent the current state of data
sig State {
	channel : Channel,
	sender : one User,
	receiver : one User
}

// Transition from one state to the next
pred State.Transition[s, s' : State] {
	// The receiver can't lose data 
	s.receiver.buffer in s'.receiver.buffer
	
}