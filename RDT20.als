module RDT10 
open util/ordering[State] 

sig Data{}

abstract sig Action {}

// An ACK action is always followed by sending new data
sig ACK extends Action {}

// An NAK action is always followed by re-transferring the last data
sig NAK extends Action {}

sig State {
	action: one Action,
	senderBuffer: set Data,
	receiverBuffer: set Data
}
{(Data = senderBuffer + receiverBuffer) and 
	(none = senderBuffer & receiverBuffer)}


pred State.start [] {
	this.action = ACK
	no this.receiverBuffer
	Data = this.senderBuffer
}

pred State.end[] {
	this.action = ACK
	no this.senderBuffer
	Data = this.receiverBuffer
}

pred Transition[s, s': State] {
	//pre/post conditions
	s.end[] or
	(
		s.action = ACK =>
			(s'.senderBuffer in s.senderBuffer and
			 s.receiverBuffer in s'.receiverBuffer and 	
			 one d : Data | d in s.senderBuffer and d in s'.receiverBuffer)

		else s.action = NAK =>
			(s'.senderBuffer = s.senderBuffer and s'.receiverBuffer = s.receiverBuffer)
	)
}

pred TraceWorking {
	first.start[]
	all s: State - last | Transition[s, s.next]
	last.end[]
}


// Milestone 2 predicate to run
pred TraceNotWorking {
	first.start[]
	all s: State - last | Transition[s, s.next]
	not last.end[]
}

run TraceWorking for 8 State, exactly 6 Data, exactly 2 Action
run TraceNotWorking for 8 State, exactly 6 Data, exactly 2 Action


//check SuccessfulTransfer for 7 State, exactly 6 Data, exactly 2 Action







