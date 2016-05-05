module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig iout, wout, din, vi1, t1in, t1out, pin, pout, t2in, t2out, win, wlout, t3wlout, t3in, vi2, t3out, wlin, vo extends Port  {
}

 fact {
   iout.tgt = t1in
   wout.tgt = win
   no din.tgt
   vi1.tgt = vi2
   t1in.tgt = t1out
   t1out.tgt = pin
   pin.tgt = pout
   pout.tgt = t2in
   t2in.tgt = t2out
   t2out.tgt = wout
   win.tgt = t3in + wlout
   wlout.tgt = wlin
   t3wlout.tgt = wlout
   t3in.tgt = t3wlout + t3out
   vi2.tgt = t3out
   t3out.tgt = din
   wlin.tgt = vo
   vo.tgt = vi1
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 18