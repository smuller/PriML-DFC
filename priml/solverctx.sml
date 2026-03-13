structure Solver :> PRIMLSOLVER =
struct

structure C = Context

(* Context to store assertions, list of constraints to check *)
type solver = C.context * IL.pconstraint list

exception SOLVER of string

fun string_of_prio p =
	    case p of
		IL.PVar v => Variable.basename v
	      | IL.PConst s => s

fun add_constraint ((ctx, cons), (p1, p2)) =
    (C.bindplecons ctx (p1, p2), cons)
    handle (C.Context s) => (print s; raise (C.Context s))

fun add_negated_constraint ((ctx, cons), (p1, p2)) =
    (ctx, (p1, p2)::cons)

fun add_comment (solver, s) =
    solver
    
fun setup constraint ctx extra_vars =
    let val orders = Context.pcons ctx
	val prios = (Context.prio_vars ctx) @ extra_vars
	val plabs = Context.plabs ctx
(*	    List.foldl
		insert_order
		SS.empty
		orders
 *)
	val ctx_with_prios =
	    List.foldl
		(fn (v, ctx) => C.bindplab ctx (Variable.basename v))
		C.empty
		prios
	val ctx_with_prios =
	    List.foldl
		(fn (k, ctx) => C.bindplab ctx k)
		C.empty
		plabs
    in
	List.foldl
	    (fn (cons, c) => add_constraint (c, cons))
	    (ctx_with_prios, [])
	    orders
    end
    handle (C.Context s) => (print s; raise (C.Context s))

fun add_negate_and_constraints ((ctx, cons), ps) =
    (ctx, ps @ cons)

val solvercalls = ref 0
val solvertime = ref (LargeInt.fromInt 0)

fun check (ctx, cons) =
    let val timer = Timer.startRealTimer ()
	val res =
	    not (List.all
		     (fn (p1, p2) => C.checkcons ctx p1 p2)
		     cons)
	    handle (C.Context s) => (print s; raise (C.Context s))
	val endtime = Timer.checkRealTimer timer
    in
	solvertime := (!solvertime) + (Time.toMicroseconds endtime);
	res
    end

end
	
		   
