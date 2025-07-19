import RiseLean.DataType
import RiseLean.Primitives
import RiseLean.Expr


#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

#check [Rise| fun(a : 3 . float, add(a)(a))]

def infer (e: RExpr) : RType := sorry
