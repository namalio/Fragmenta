module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig sw, win, wout, dwi, wl, wlo, wli, vo, vi2, vi1 extends Port  {
}

 fact {
   sw.tgt = win
   win.tgt = wout
   wout.tgt = dwi
   no dwi.tgt
   wl.tgt = wlo
   wlo.tgt = wli
   wli.tgt = vo
   vo.tgt = vi2
   vi2.tgt = vi1
   vi1.tgt = wout
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 10