fact {
  some s, s' : State, caller, callee : Address | 
  s.audio = caller and 
  s'.audio = callee and 
  caller not in callee and 
  s not in s' and
  s.calls[caller] != s'.calls[callee]
}