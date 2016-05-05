module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t15wi, t15wo, t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t15wlo, t15vi extends Port  {
}

 fact {
   t15wi.tgt = t15wo + t15wlo
   t15wo.tgt = dwi
   t14wi.tgt = t14wo
   t14wo.tgt = t15wi
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
   sw.tgt = t15wi
   cwli.tgt = cvo
   cvo.tgt = t15vi
   no dwi.tgt
   t15wlo.tgt = cwli
   t15vi.tgt = t15wo
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 36