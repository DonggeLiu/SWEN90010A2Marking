fact {
    all s, s' : State |
    (ord/next[s] = s') => ((no s.last_called) or (s.last_called = s'.last_called))
}

check no_bad_states for 8 expect 1

