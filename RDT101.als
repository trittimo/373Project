module RDT10 
open util/ordering[State] 

sig Data{} 

sig User {
	buffer: set Data
}

sig State {
	sender: one User, 
	receiver: one User
}

fact {
	no s: State | s.sender = s.receiver 
	all s: State | Data = s.sender.buffer + s.receiver.buffer 
}

pred State.start[] {
	all d: Data | d in this.sender.buffer
	no d: Data | d in this.receiver.buffer 
}

pred State.end[] {
	no d: Data | d in this.sender.buffer
	all d: Data | d in this.receiver.buffer
}


//one data moves from s.sender -> s'.reciever in a state 
pred Transition [s, s': State] {
	//pre and post conditions 
	s.receiver.buffer in s'.receiver.buffer
	s'.sender.buffer in s.sender.buffer

	//move 1 piece of data 
//	lone d : Data | d in s.sender.buffer and d in s'.receiver.buffer
//	lone d : Data | s'.sender.buffer = s.sender.buffer - d
//	lone d : Data | s.receiver.buffer = s'.receiver.buffer - d 
	
}


pred test[] {
	first.start 
	Transition[first, first.next]
}


run test for exactly 2 State, exactly 6 Data, 2 User
run end for exactly 1 State, exactly 6 Data, 2 User 
run start for exactly 1 State, exactly 6 Data, 2 User 










