module RDT10 
open util/ordering[State] 

// The thing to be sent
abstract sig Payload {}

// The payload transfer was successful
lone sig ACK extends Payload {}

// The payload transfer was not successful
lone sig NAK extends Payload {}

// The actual data to be sent
sig Data extends Payload {}

abstract sig Checksum {}
lone sig GoodChecksum extends Checksum {}
lone sig BadChecksum extends Checksum {}

// A packet is what is sent over the wire
sig Packet {
	checksum: one Checksum,
	payload: one Payload
}

sig State {
	// The sender's buffer
	senderBuffer: set Data,

	// The receiver's buffer
	receiverBuffer: set Data,

	// The channel over which we are sending a packet
	packet: lone Packet,

	// The last piece of data we attempted to transfer
	lastSent: lone Data
}

pred isCorrupt[p: Packet] {
	p.checksum = BadChecksum
}

pred makePacket[p: Packet, pa: Payload] {
	p.payload = pa and
	p.checksum in Checksum
}

pred Skip[s, s': State] {
	s.senderBuffer = s'.senderBuffer and
	s.receiverBuffer = s'.receiverBuffer and
	s.packet = s'.packet and
	s.lastSent = s'.lastSent
}

pred isData[p: Packet] {
	p.payload in Data
}

pred isAck[p: Packet] {
	p.payload in ACK
}

pred isNak[p: Packet] {
	p.payload in NAK
}

pred SendNewData[s, s': State] {
	one p: Packet, d: s.senderBuffer | 
		makePacket[p, d] and
		s'.packet = p and
		s'.lastSent = d and
		s'.senderBuffer = s.senderBuffer - d and
		s'.receiverBuffer = s.receiverBuffer
}

pred ResendData[s, s': State] {
	one p: Packet |
		makePacket[p, s.lastSent] and
		s'.packet = p and
		s'.lastSent = s.lastSent and
		s.senderBuffer = s'.senderBuffer and
		s.receiverBuffer = s'.receiverBuffer
}

pred SendNak[s, s' : State] {
	one p: Packet|
		makePacket[p, NAK] and
		s'.packet = p and
		s'.lastSent = s.lastSent
}

pred SendAck[s, s' : State] {
	one p: Packet |
		makePacket[p, ACK] and
		s'.packet = p and
		s'.receiverBuffer = s.receiverBuffer + s.lastSent
}

pred NoDataLoss[s, s': State] {
	s'.senderBuffer in s.senderBuffer and
	s.receiverBuffer in s'.receiverBuffer
}

pred NoBufferChange[s, s': State] {
	s'.senderBuffer = s.senderBuffer and
	s'.receiverBuffer = s.receiverBuffer
}

pred Transition[s, s': State] {
	NoDataLoss[s, s'] and
	(
		no s.packet => (
			no s.senderBuffer => 
				Skip[s, s']
			else
				SendNewData[s, s']
		)
		else (
			isData[s.packet] => (
				isCorrupt[s.packet] => (
					SendNak[s, s'] and
					NoBufferChange[s, s'])
				else
					(SendAck[s, s'])
			)
			else isCorrupt[s.packet] => (
				// Enter a state of deadlock if the Nak packet is corrupt
				Skip[s, s']
			)
			else isAck[s.packet] => (
				// Send the next data
				SendNewData[s, s']
			)
			else (
				// Retransmit the last data sent
				ResendData[s, s']
			)
		)
	)
}

pred State.start[] {
	no this.lastSent
	no this.receiverBuffer
	Data = this.senderBuffer
	no this.packet
}

pred State.end[] {
	no this.senderBuffer
	Data = this.receiverBuffer
}

pred Test {
	first.start
	Transition[first, first.next]
	Transition[first.next, first.next.next]
	last.end[]
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

// run Test for exactly 3 State, exactly 1 Data, exactly 2 Checksum, exactly 2 Packet, exactly 3 Payload
// run TraceWorking for 10 State, exactly 5 Payload, exactly 8 Packet
//run TraceNotWorking for 16 State, exactly 6 Data, 12 Packet
