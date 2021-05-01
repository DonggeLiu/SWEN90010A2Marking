fact {
  all s, s' : State, caller, callee : Address | 
  (s.audio=caller and s'.audio=callee) 
  implies 
  (s.audio = s'.audio or s.calls[caller] = s'.calls[callee])
}