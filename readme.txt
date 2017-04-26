CSSE 373 Formal Methods
Verification of the Reliable Data Transfer Protocol
Authored by Michael Trittin and Vibha Alangar
===================================================
Following are the assumptions we make regarding the protocol

1. The data transfer happens between one sender and one receiver only
2. Both sender and receiver have their own buffer that can hold a set of data
3. A transfer is reliably completed if the receiver buffer eventually receives
   all of the data initially present in the sender's buffer.