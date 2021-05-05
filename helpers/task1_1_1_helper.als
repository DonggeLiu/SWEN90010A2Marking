// =========== Task 1.1.send =========== 

pred user_send_post_correct[m : Message, s : State, s' : State] {
	s'.network = m and
  (
	(m.type in SDPOffer and 
	s'.calls = s.calls ++ (m.dest -> SignallingOffered) and 
	s'.audio = s.audio and 
	s'.ringing = s.ringing) or
	(m.type in SDPAnswer and 
	s'.calls = s.calls ++ (m.dest -> SignallingAnswered) and 
	s'.audio = s.audio and 
	s'.ringing = s.ringing) or
	(m.type in SDPCandidates and 
	s'.calls = s.calls ++ (m.dest -> SignallingComplete) and 
	s'.audio = s.audio and 
	s'.ringing = s.ringing) or
	(m.type in Connect and s'.calls = s.calls ++ (m.dest -> Answered) and s'.audio = m.dest and no s'.ringing)
	// (m.type in Connect and 
	// s'.calls = s.calls and 
	// s'.audio = m.dest and 
	// s'.ringing = s.ringing)
  )
}

fact { all s, s' : State | s.last_answered = s'.last_answered and s.last_called = s'.last_called}

assert TASK1_1_send_CORRECT {
	all m : Message, s, s' : State |
	user_send_pre[m, s] =>
	(
		user_send_post_correct[m, s, s'] <=> user_send_post[m, s, s']
	)
}
check TASK1_1_send_CORRECT for 10 but 4 Address
