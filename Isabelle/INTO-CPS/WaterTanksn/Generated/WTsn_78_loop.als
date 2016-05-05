module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t78wi, t78wo, t77wi, t77wo, t76wi, t76wo, t75wi, t75wo, t74wi, t74wo, t73wi, t73wo, t72wi, t72wo, t71wi, t71wo, t70wi, t70wo, t69wi, t69wo, t68wi, t68wo, t67wi, t67wo, t66wi, t66wo, t65wi, t65wo, t64wi, t64wo, t63wi, t63wo, t62wi, t62wo, t61wi, t61wo, t60wi, t60wo, t59wi, t59wo, t58wi, t58wo, t57wi, t57wo, t56wi, t56wo, t55wi, t55wo, t54wi, t54wo, t53wi, t53wo, t52wi, t52wo, t51wi, t51wo, t50wi, t50wo, t49wi, t49wo, t48wi, t48wo, t47wi, t47wo, t46wi, t46wo, t45wi, t45wo, t44wi, t44wo, t43wi, t43wo, t42wi, t42wo, t41wi, t41wo, t40wi, t40wo, t39wi, t39wo, t38wi, t38wo, t37wi, t37wo, t36wi, t36wo, t35wi, t35wo, t34wi, t34wo, t33wi, t33wo, t32wi, t32wo, t31wi, t31wo, t30wi, t30wo, t29wi, t29wo, t28wi, t28wo, t27wi, t27wo, t26wi, t26wo, t25wi, t25wo, t24wi, t24wo, t23wi, t23wo, t22wi, t22wo, t21wi, t21wo, t20wi, t20wo, t19wi, t19wo, t18wi, t18wo, t17wi, t17wo, t16wi, t16wo, t15wi, t15wo, t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t78wlo, t78vi, dwo extends Port  {
}

 fact {
   t78wi.tgt = t78wo + t78wlo
   t78wo.tgt = dwi
   t77wi.tgt = t77wo
   t77wo.tgt = t78wi
   t76wi.tgt = t76wo
   t76wo.tgt = t77wi
   t75wi.tgt = t75wo
   t75wo.tgt = t76wi
   t74wi.tgt = t74wo
   t74wo.tgt = t75wi
   t73wi.tgt = t73wo
   t73wo.tgt = t74wi
   t72wi.tgt = t72wo
   t72wo.tgt = t73wi
   t71wi.tgt = t71wo
   t71wo.tgt = t72wi
   t70wi.tgt = t70wo
   t70wo.tgt = t71wi
   t69wi.tgt = t69wo
   t69wo.tgt = t70wi
   t68wi.tgt = t68wo
   t68wo.tgt = t69wi
   t67wi.tgt = t67wo
   t67wo.tgt = t68wi
   t66wi.tgt = t66wo
   t66wo.tgt = t67wi
   t65wi.tgt = t65wo
   t65wo.tgt = t66wi
   t64wi.tgt = t64wo
   t64wo.tgt = t65wi
   t63wi.tgt = t63wo
   t63wo.tgt = t64wi
   t62wi.tgt = t62wo
   t62wo.tgt = t63wi
   t61wi.tgt = t61wo
   t61wo.tgt = t62wi
   t60wi.tgt = t60wo
   t60wo.tgt = t61wi
   t59wi.tgt = t59wo
   t59wo.tgt = t60wi
   t58wi.tgt = t58wo
   t58wo.tgt = t59wi
   t57wi.tgt = t57wo
   t57wo.tgt = t58wi
   t56wi.tgt = t56wo
   t56wo.tgt = t57wi
   t55wi.tgt = t55wo
   t55wo.tgt = t56wi
   t54wi.tgt = t54wo
   t54wo.tgt = t55wi
   t53wi.tgt = t53wo
   t53wo.tgt = t54wi
   t52wi.tgt = t52wo
   t52wo.tgt = t53wi
   t51wi.tgt = t51wo
   t51wo.tgt = t52wi
   t50wi.tgt = t50wo
   t50wo.tgt = t51wi
   t49wi.tgt = t49wo
   t49wo.tgt = t50wi
   t48wi.tgt = t48wo
   t48wo.tgt = t49wi
   t47wi.tgt = t47wo
   t47wo.tgt = t48wi
   t46wi.tgt = t46wo
   t46wo.tgt = t47wi
   t45wi.tgt = t45wo
   t45wo.tgt = t46wi
   t44wi.tgt = t44wo
   t44wo.tgt = t45wi
   t43wi.tgt = t43wo
   t43wo.tgt = t44wi
   t42wi.tgt = t42wo
   t42wo.tgt = t43wi
   t41wi.tgt = t41wo
   t41wo.tgt = t42wi
   t40wi.tgt = t40wo
   t40wo.tgt = t41wi
   t39wi.tgt = t39wo
   t39wo.tgt = t40wi
   t38wi.tgt = t38wo
   t38wo.tgt = t39wi
   t37wi.tgt = t37wo
   t37wo.tgt = t38wi
   t36wi.tgt = t36wo
   t36wo.tgt = t37wi
   t35wi.tgt = t35wo
   t35wo.tgt = t36wi
   t34wi.tgt = t34wo
   t34wo.tgt = t35wi
   t33wi.tgt = t33wo
   t33wo.tgt = t34wi
   t32wi.tgt = t32wo
   t32wo.tgt = t33wi
   t31wi.tgt = t31wo
   t31wo.tgt = t32wi
   t30wi.tgt = t30wo
   t30wo.tgt = t31wi
   t29wi.tgt = t29wo
   t29wo.tgt = t30wi
   t28wi.tgt = t28wo
   t28wo.tgt = t29wi
   t27wi.tgt = t27wo
   t27wo.tgt = t28wi
   t26wi.tgt = t26wo
   t26wo.tgt = t27wi
   t25wi.tgt = t25wo
   t25wo.tgt = t26wi
   t24wi.tgt = t24wo
   t24wo.tgt = t25wi
   t23wi.tgt = t23wo
   t23wo.tgt = t24wi
   t22wi.tgt = t22wo
   t22wo.tgt = t23wi
   t21wi.tgt = t21wo
   t21wo.tgt = t22wi
   t20wi.tgt = t20wo
   t20wo.tgt = t21wi
   t19wi.tgt = t19wo
   t19wo.tgt = t20wi
   t18wi.tgt = t18wo
   t18wo.tgt = t19wi
   t17wi.tgt = t17wo
   t17wo.tgt = t18wi
   t16wi.tgt = t16wo
   t16wo.tgt = t17wi
   t15wi.tgt = t15wo
   t15wo.tgt = t16wi
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
   sw.tgt = t78wi
   cwli.tgt = cvo
   cvo.tgt = t78vi
   dwi.tgt = dwo
   t78wlo.tgt = cwli
   t78vi.tgt = t78wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 163