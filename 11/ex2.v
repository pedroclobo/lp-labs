From Lab11 Require Import ulc.

(* Check ulc.v for the definition of `subst`. *)

(* x[x:=y] *)
Compute <{[x:=y] x}>.

(* y[x:=y] *)
Compute <{[x:=y] y}>.

(* (λ  x . y x) [x:=y] *)
(* should stay the same, as x is a bound variable *)
Compute <{[x:=y] λ x . y x}>.

(* (λ  y . y x) [x:=y] *)
Compute <{[x:=y] λ y . y x}>.

(* (λ  y . (λ  x . w x y)) [x:=y] *)
(* should stay the same, as x is a bound variable *)
Compute <{[x:=y] λ y . λ x . w x y}>.

(* (λ  y . (λ  x . w x y)) [w:=y] *)
Compute <{[w:=y] λ y . λ x . w x y}>.

(* (λ  y . (λ  x . w x y)) [w:=x] *)
Compute <{[w:=x] λ y . λ x . w x y}>.
