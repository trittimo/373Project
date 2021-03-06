module RDT10 
open util/ordering[State] 

sig Data{}

// A ACK packet is always followed by sending new data
sig ACK extends Data {}

// A NAK packet is always followed by re-transferring the last data
sig NAK extends Data {
	appliesTo: one Data
}

sig File extends Data {}

abstract sig Checksum {}
lone sig GoodChecksum extends Checksum {}
lone sig BadChecksum extends Checksum {}

// A packet is what is sent over the wire
// The checksum can be either good, or bad
sig Packet {
	checksum: one Checksum,
	data: one Data
}

sig State {
	// The sender's buffer
	senderBuffer: set File,

	// The receiver's buffer
	receiverBuffer: set File,

	// The packet currently being transmitted
	packet: lone Packet
}

// There is no data that exists outside of the sender's buffer + receiver's buffer
// And there is no data in the sender/receiver's buffer intersection
fact DataWholeness {
	all s : State | (File = s.senderBuffer + s.receiverBuffer and
						  none = s.senderBuffer & s.receiverBuffer)
}

// Initially, we aren't sending anything
pred State.start [] {
	no this.receiverBuffer
	File = this.senderBuffer
	no this.packet
}

// We've sent everything
pred State.end[] {
	no this.senderBuffer
	File = this.receiverBuffer
}

fact {
	no d : File | d in State.receiverBuffer and d not in Packet.data
}

pred Transition[s, s': State] {
	// Some rules regarding the state, no matter what the stat consists of
	// The new sender buffer will always be a subset of the old sender buffer
	s'.senderBuffer in s.senderBuffer and
	s.receiverBuffer in s'.receiverBuffer and
	(not s.start[] => one s.packet) and

	// Several conditions we have to care about
	(
		// Secondly, if there is no packet currently in transmission, go ahead and send data
		// from the sender buffer in the next state
		no s.packet =>
			(one d : File |
				d in s.senderBuffer and
				d in s'.packet.data)
		
		// Firstly, if the last packet sent was corrupted, and the packet was ACK or NAK
		// Put the system into deadlock
		else s.packet.checksum in BadChecksum and (s.packet.data in (ACK + NAK)) =>
			s = s'

		// Thirdly, if the last packet sent was an ACK, send the next bit of data
		else s.packet.data in ACK =>
			(one d : File |
				d in s.senderBuffer and
				d in s'.packet.data)

		// Thirdly, if the last packet sent was a NAK, resend the last data that we sent (i.e. the appliedTo)
		else s.packet.data in NAK =>
			s'.packet.data = s.packet.data.appliesTo

		// Lastly, if the last packet was corrupted, send a NAK
		else s.packet.checksum in BadChecksum =>
			(s'.packet.data in NAK and
			s'.packet.data.appliesTo = s.packet.data)

		// Otherwise, send an ACK, and remove the data from sender buffer and add to receiver buffer
		else s.packet.checksum in GoodChecksum =>
			(s'.packet.data in ACK and
			s.packet.data not in s'.senderBuffer and
			s.packet.data in s'.receiverBuffer)
	)
}

pred Test {
	first.start[]
	Transition[first, first.next]
	Transition[first.next, first.next.next]
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

//run Test for exactly 3 State, exactly 3 Data, exactly 1 ACK, exactly 1 NAK, 2 Packet
run TraceWorking for 10 State, exactly 5 Data, exactly 1 ACK, exactly 4 File, exactly 8 Packet
run TraceNotWorking for 16 State, exactly 6 Data, 12 Packet
