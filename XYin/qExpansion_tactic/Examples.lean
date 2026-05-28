import XYin.qExpansion_tactic.Qj

set_option linter.style.longLine false

open XYin.qExpansion_tactic
open scoped XYin.qExpansion_tactic

#qexp qj coeff 4
#qexp qj precision 4
#eval qjCoeffInt 4
#eval qjCoeffsUpTo 4

#qexp Delta coeff 4
#qexp Delta precision 4
#eval deltaCoeffInt 4
#eval deltaCoeffsUpTo 4

#check qexp_coeff qj 4
#check qexp_coeff qj 4 864299970
#check qexp_coeff qj 9 401490886656000

example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4

example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4 864299970

example : qj_qexpansion.coeff 9 = 401490886656000 := qexp_coeff qj 9 401490886656000

#check qexp_coeff Delta 4
#check qexp_coeff Delta 4 (-1472)

example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4

example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4 (-1472)
