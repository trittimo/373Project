module RDT10 
open util/ordering[State] 

sig Data{} 

sig State {
	senderBuffer: set Data,
	receiverBuffer: set Data
}
{(Data = senderBuffer + receiverBuffer) and 
	(none = senderBuffer & receiverBuffer)}


pred State.start [] {
	#(this.receiverBuffer) = 0
	Data = this.senderBuffer
}

pred State.end[] {
	#(this.senderBuffer) = 0
	Data = this.receiverBuffer
}

pred Transition[s, s': State] {
	//pre/post conditions
	s.end[] or 
 
	(s'.senderBuffer in s.senderBuffer and
	s.receiverBuffer in s'.receiverBuffer and 	
	one d : Data | d in s.senderBuffer and d in s'.receiverBuffer)

}

pred TraceWorking[] {
	first.start[] 
	all s: State - last | Transition[s, s.next] 
	last.end[]
}


run TraceWorking for 7 State, exactly 6 Data
run end for exactly 1 State, exactly 6 Data
run start for exactly 1 State, exactly 6 Data











