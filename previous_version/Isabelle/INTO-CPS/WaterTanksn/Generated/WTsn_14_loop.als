module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t14wlo, t14vi, dwo extends Port  {
}

 fact {
   t14wi.tgt = t14wo + t14wlo
   t14wo.tgt = dwi
   t13wi.tgt = t13wo
   t13wo.tgt = t14wi
   t12wi.tgt = t12wo
   t12wo.tgt = t13wi
   t11wi.tgt = t11wo
   t11wo.tgt = t12wi
   t10wi.tgt = t10wo
   t10wo.tgt = t11wi
   t9wi.tgt = t9wo
   t9wo.tgt = t10wi
   t8wi.tgt = t8wo
   t8wo.tgt = t9wi
   t7wi.tgt = t7wo
   t7wo.tgt = t8wi
   t6wi.tgt = t6wo
   t6wo.tgt = t7wi
   t5wi.tgt = t5wo
   t5wo.tgt = t6wi
   t4wi.tgt = t4wo
   t4wo.tgt = t5wi
   t3wi.tgt = t3wo
   t3wo.tgt = t4wi
   t2wi.tgt = t2wo
   t2wo.tgt = t3wi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t14wi
   cwli.tgt = cvo
   cvo.tgt = t14vi
   dwi.tgt = dwo
   t14wlo.tgt = cwli
   t14vi.tgt = t14wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 35