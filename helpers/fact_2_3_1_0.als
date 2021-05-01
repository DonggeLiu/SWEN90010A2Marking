pred did_not_call {all s: State | no s.last_called}
pred did_not_connect {all s: State | no s.audio}
fact {did_not_call or did_not_connect}


// fact {all s, s': State | not no s.last_called or no s'.audio}

