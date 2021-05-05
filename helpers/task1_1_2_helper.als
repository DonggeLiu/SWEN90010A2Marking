// =========== Task 1.1.receive =========== 

pred user_recv_post_correct[m : Message, s : State, s' : State] {
  no s'.network and
  (
    (m.type in SDPOffer and s'.calls = s.calls ++ (m.source -> SignallingStart) and s'.audio = s.audio and s'.ringing = s.ringing) or // and s'.audio = s.audio and s'.ringing = s.ringing) or
    (m.type in SDPAnswer and s'.calls = s.calls ++ (m.source -> SignallingOngoing) and s'.audio = s.audio and s'.ringing = s.ringing) or // and s'.audio = s.audio and s'.ringing = s.ringing) or
    (m.type in SDPCandidates and s'.calls = s.calls ++ (m.source -> SignallingComplete) and s'.ringing = m.source and s'.audio = s.audio) or// and s'.audio = s.audio and s'.ringing = m.source) or
    (m.type in Connect and s'.audio = m.source and s'.ringing = s.ringing and s'.calls = s.calls)
  )
}

fact { all s, s' : State | s.last_answered = s'.last_answered and s.last_called = s'.last_called}

assert TASK1_1_recv_CORRECT {
	all m : Message, s, s' : State |
  user_recv_pre[m, s] =>
	(
		user_recv_post_correct[m, s, s'] <=> user_recv_post[m, s, s']
	)
}
check TASK1_1_recv_CORRECT for 10 but 4 Address
