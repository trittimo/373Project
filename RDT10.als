module RDT10
open util/ordering[State]

// Data which can be sent across the network
// The contents of the data doesn't actually matter
// Synonymous in this case with a packet
sig Data {}

// A reliable channel to send data across
sig Channel {
	// The data we intend to send
	data : lone Data
}

// Used to represent a sender or a receiver
sig User {
	buffer : set Data
}

// Used to represent the current state of data
sig State {
	channel : one Channel,
	sender : one User,
	receiver : one User
}

fact DataModel {
	all s : State | Data = s.receiver.buffer + s.sender.buffer + s.channel.data
}

// Transition from one state to the next
pred Transition[s, s' : State] {
	s.receiver.buffer in s'.receiver.buffer
	one  s.sender.buffer - s'.reciever.buffer
	one  s'.sender.buffer = s.sender.buffer - s.sender.buffer - s'.reciever.buffer

	// new receiver buffer = old receiver buffer + old channel data
	//s'.receiver.buffer = s.receiver.buffer + s.channel.data

	// new channel data in old sender buffer
	//s'.channel.data in s.sender.buffer

	// new sender buffer = old sender buffer - new channel data
	//s'.sender.buffer = s.sender.buffer - s'.channel.data
}

pred Progress[s, s' : State] {
	#s'.receiver.buffer > #s.receiver.buffer or s'.end[]
}

fact UserModel {
	no s : State | s.sender = s.receiver
}

pred State.start[] {
	Data = this.sender.buffer
	no this.receiver.buffer
	no this.channel.data
}

pred State.end[] {
	no this.sender.buffer
	no this.channel.data
	Data = this.receiver.buffer
}

pred Trace[] {
	first.start[]
	all s : State - last | Transition[s, s.next] and Progress[s, s.next]
	last.end[]
}

run Trace for 10 State, exactly 6 Data, exactly 1 Channel, exactly 2 User
run start for exactly 1 State, exactly 6 Data, exactly 1 Channel, exactly 2 User
run end for exactly 1 State, exactly 6 Data, exactly 1 Channel, exactly 2 User
