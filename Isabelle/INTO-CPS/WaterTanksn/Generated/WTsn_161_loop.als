module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t161wi, t161wo, t160wi, t160wo, t159wi, t159wo, t158wi, t158wo, t157wi, t157wo, t156wi, t156wo, t155wi, t155wo, t154wi, t154wo, t153wi, t153wo, t152wi, t152wo, t151wi, t151wo, t150wi, t150wo, t149wi, t149wo, t148wi, t148wo, t147wi, t147wo, t146wi, t146wo, t145wi, t145wo, t144wi, t144wo, t143wi, t143wo, t142wi, t142wo, t141wi, t141wo, t140wi, t140wo, t139wi, t139wo, t138wi, t138wo, t137wi, t137wo, t136wi, t136wo, t135wi, t135wo, t134wi, t134wo, t133wi, t133wo, t132wi, t132wo, t131wi, t131wo, t130wi, t130wo, t129wi, t129wo, t128wi, t128wo, t127wi, t127wo, t126wi, t126wo, t125wi, t125wo, t124wi, t124wo, t123wi, t123wo, t122wi, t122wo, t121wi, t121wo, t120wi, t120wo, t119wi, t119wo, t118wi, t118wo, t117wi, t117wo, t116wi, t116wo, t115wi, t115wo, t114wi, t114wo, t113wi, t113wo, t112wi, t112wo, t111wi, t111wo, t110wi, t110wo, t109wi, t109wo, t108wi, t108wo, t107wi, t107wo, t106wi, t106wo, t105wi, t105wo, t104wi, t104wo, t103wi, t103wo, t102wi, t102wo, t101wi, t101wo, t100wi, t100wo, t99wi, t99wo, t98wi, t98wo, t97wi, t97wo, t96wi, t96wo, t95wi, t95wo, t94wi, t94wo, t93wi, t93wo, t92wi, t92wo, t91wi, t91wo, t90wi, t90wo, t89wi, t89wo, t88wi, t88wo, t87wi, t87wo, t86wi, t86wo, t85wi, t85wo, t84wi, t84wo, t83wi, t83wo, t82wi, t82wo, t81wi, t81wo, t80wi, t80wo, t79wi, t79wo, t78wi, t78wo, t77wi, t77wo, t76wi, t76wo, t75wi, t75wo, t74wi, t74wo, t73wi, t73wo, t72wi, t72wo, t71wi, t71wo, t70wi, t70wo, t69wi, t69wo, t68wi, t68wo, t67wi, t67wo, t66wi, t66wo, t65wi, t65wo, t64wi, t64wo, t63wi, t63wo, t62wi, t62wo, t61wi, t61wo, t60wi, t60wo, t59wi, t59wo, t58wi, t58wo, t57wi, t57wo, t56wi, t56wo, t55wi, t55wo, t54wi, t54wo, t53wi, t53wo, t52wi, t52wo, t51wi, t51wo, t50wi, t50wo, t49wi, t49wo, t48wi, t48wo, t47wi, t47wo, t46wi, t46wo, t45wi, t45wo, t44wi, t44wo, t43wi, t43wo, t42wi, t42wo, t41wi, t41wo, t40wi, t40wo, t39wi, t39wo, t38wi, t38wo, t37wi, t37wo, t36wi, t36wo, t35wi, t35wo, t34wi, t34wo, t33wi, t33wo, t32wi, t32wo, t31wi, t31wo, t30wi, t30wo, t29wi, t29wo, t28wi, t28wo, t27wi, t27wo, t26wi, t26wo, t25wi, t25wo, t24wi, t24wo, t23wi, t23wo, t22wi, t22wo, t21wi, t21wo, t20wi, t20wo, t19wi, t19wo, t18wi, t18wo, t17wi, t17wo, t16wi, t16wo, t15wi, t15wo, t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t161wlo, t161vi, dwo extends Port  {
}

 fact {
   t161wi.tgt = t161wo + t161wlo
   t161wo.tgt = dwi
   t160wi.tgt = t160wo
   t160wo.tgt = t161wi
   t159wi.tgt = t159wo
   t159wo.tgt = t160wi
   t158wi.tgt = t158wo
   t158wo.tgt = t159wi
   t157wi.tgt = t157wo
   t157wo.tgt = t158wi
   t156wi.tgt = t156wo
   t156wo.tgt = t157wi
   t155wi.tgt = t155wo
   t155wo.tgt = t156wi
   t154wi.tgt = t154wo
   t154wo.tgt = t155wi
   t153wi.tgt = t153wo
   t153wo.tgt = t154wi
   t152wi.tgt = t152wo
   t152wo.tgt = t153wi
   t151wi.tgt = t151wo
   t151wo.tgt = t152wi
   t150wi.tgt = t150wo
   t150wo.tgt = t151wi
   t149wi.tgt = t149wo
   t149wo.tgt = t150wi
   t148wi.tgt = t148wo
   t148wo.tgt = t149wi
   t147wi.tgt = t147wo
   t147wo.tgt = t148wi
   t146wi.tgt = t146wo
   t146wo.tgt = t147wi
   t145wi.tgt = t145wo
   t145wo.tgt = t146wi
   t144wi.tgt = t144wo
   t144wo.tgt = t145wi
   t143wi.tgt = t143wo
   t143wo.tgt = t144wi
   t142wi.tgt = t142wo
   t142wo.tgt = t143wi
   t141wi.tgt = t141wo
   t141wo.tgt = t142wi
   t140wi.tgt = t140wo
   t140wo.tgt = t141wi
   t139wi.tgt = t139wo
   t139wo.tgt = t140wi
   t138wi.tgt = t138wo
   t138wo.tgt = t139wi
   t137wi.tgt = t137wo
   t137wo.tgt = t138wi
   t136wi.tgt = t136wo
   t136wo.tgt = t137wi
   t135wi.tgt = t135wo
   t135wo.tgt = t136wi
   t134wi.tgt = t134wo
   t134wo.tgt = t135wi
   t133wi.tgt = t133wo
   t133wo.tgt = t134wi
   t132wi.tgt = t132wo
   t132wo.tgt = t133wi
   t131wi.tgt = t131wo
   t131wo.tgt = t132wi
   t130wi.tgt = t130wo
   t130wo.tgt = t131wi
   t129wi.tgt = t129wo
   t129wo.tgt = t130wi
   t128wi.tgt = t128wo
   t128wo.tgt = t129wi
   t127wi.tgt = t127wo
   t127wo.tgt = t128wi
   t126wi.tgt = t126wo
   t126wo.tgt = t127wi
   t125wi.tgt = t125wo
   t125wo.tgt = t126wi
   t124wi.tgt = t124wo
   t124wo.tgt = t125wi
   t123wi.tgt = t123wo
   t123wo.tgt = t124wi
   t122wi.tgt = t122wo
   t122wo.tgt = t123wi
   t121wi.tgt = t121wo
   t121wo.tgt = t122wi
   t120wi.tgt = t120wo
   t120wo.tgt = t121wi
   t119wi.tgt = t119wo
   t119wo.tgt = t120wi
   t118wi.tgt = t118wo
   t118wo.tgt = t119wi
   t117wi.tgt = t117wo
   t117wo.tgt = t118wi
   t116wi.tgt = t116wo
   t116wo.tgt = t117wi
   t115wi.tgt = t115wo
   t115wo.tgt = t116wi
   t114wi.tgt = t114wo
   t114wo.tgt = t115wi
   t113wi.tgt = t113wo
   t113wo.tgt = t114wi
   t112wi.tgt = t112wo
   t112wo.tgt = t113wi
   t111wi.tgt = t111wo
   t111wo.tgt = t112wi
   t110wi.tgt = t110wo
   t110wo.tgt = t111wi
   t109wi.tgt = t109wo
   t109wo.tgt = t110wi
   t108wi.tgt = t108wo
   t108wo.tgt = t109wi
   t107wi.tgt = t107wo
   t107wo.tgt = t108wi
   t106wi.tgt = t106wo
   t106wo.tgt = t107wi
   t105wi.tgt = t105wo
   t105wo.tgt = t106wi
   t104wi.tgt = t104wo
   t104wo.tgt = t105wi
   t103wi.tgt = t103wo
   t103wo.tgt = t104wi
   t102wi.tgt = t102wo
   t102wo.tgt = t103wi
   t101wi.tgt = t101wo
   t101wo.tgt = t102wi
   t100wi.tgt = t100wo
   t100wo.tgt = t101wi
   t99wi.tgt = t99wo
   t99wo.tgt = t100wi
   t98wi.tgt = t98wo
   t98wo.tgt = t99wi
   t97wi.tgt = t97wo
   t97wo.tgt = t98wi
   t96wi.tgt = t96wo
   t96wo.tgt = t97wi
   t95wi.tgt = t95wo
   t95wo.tgt = t96wi
   t94wi.tgt = t94wo
   t94wo.tgt = t95wi
   t93wi.tgt = t93wo
   t93wo.tgt = t94wi
   t92wi.tgt = t92wo
   t92wo.tgt = t93wi
   t91wi.tgt = t91wo
   t91wo.tgt = t92wi
   t90wi.tgt = t90wo
   t90wo.tgt = t91wi
   t89wi.tgt = t89wo
   t89wo.tgt = t90wi
   t88wi.tgt = t88wo
   t88wo.tgt = t89wi
   t87wi.tgt = t87wo
   t87wo.tgt = t88wi
   t86wi.tgt = t86wo
   t86wo.tgt = t87wi
   t85wi.tgt = t85wo
   t85wo.tgt = t86wi
   t84wi.tgt = t84wo
   t84wo.tgt = t85wi
   t83wi.tgt = t83wo
   t83wo.tgt = t84wi
   t82wi.tgt = t82wo
   t82wo.tgt = t83wi
   t81wi.tgt = t81wo
   t81wo.tgt = t82wi
   t80wi.tgt = t80wo
   t80wo.tgt = t81wi
   t79wi.tgt = t79wo
   t79wo.tgt = t80wi
   t78wi.tgt = t78wo
   t78wo.tgt = t79wi
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
   sw.tgt = t161wi
   cwli.tgt = cvo
   cvo.tgt = t161vi
   dwi.tgt = dwo
   t161wlo.tgt = cwli
   t161vi.tgt = t161wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 329