fact {
    all s, s' : State |
    (ord/next[s] = s') => ((no s.last_called) or (s.last_called = s'.last_called))
}

fact {
  all m : Message, s : State |
  (
    m in s.network and
    m.dest in UserAddress and
    s.calls[m.source] = SignallingComplete 
    and 
    m.type in Connect
  ) => no s.ringing //FIX: must not be ringing

}

check no_bad_states for 8
