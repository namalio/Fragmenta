module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig win, v1, v2, w, win1, wout1, win2, wout2, win3, wout3 extends Port  {
}

 fact {
   win.tgt = v1
   v1.tgt = v2
   v2.tgt = w
   w.tgt = win1
   win1.tgt = wout1
   wout1.tgt = win2
   win2.tgt = wout2
   wout2.tgt = win3
   win3.tgt = wout3
   wout3.tgt = win
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 10