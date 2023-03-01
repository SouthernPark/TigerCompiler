signature SEMANT =
sig
  val transProg: Absyn.exp -> unit
end

structure Semant :> SEMANT =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  type venv = Env.enventry S.table
  type tenv = T.ty S.table
  type expty = {exp: Translate.exp, ty: T.ty}

  val error = ErrorMsg.error (* open error defined in errormsg.sml *)

  fun size ([]) = 0
    | size (a::l) = 1 + size(l)

  (* isSubTy(t1, t2) checks if t1 is a subtype of t2, same type is also regarded as sub_type *)
  fun isSubTy (T.IMPOSSIBILITY, _) = true
    | isSubTy (_, T.UNIT) = true
    | isSubTy (T.NIL, T.RECORD(lst, _)) = true
    | isSubTy (T.INT, T.INT) = true
    | isSubTy (T.STRING, T.STRING) = true
    | isSubTy (T.NIL, T.NIL) = true
    | isSubTy (T.ARRAY(t1, ref1), T.ARRAY(t2, ref2)) = (ref1 = ref2)
    | isSubTy (T.RECORD(lst1, ref1), T.RECORD(lst2, ref2)) = (ref1 = ref2)
    | isSubTy (t1, t2) = false

  fun leastUpperBound (t, T.IMPOSSIBILITY) = t
    | leastUpperBound (T.IMPOSSIBILITY, t) = t
    | leastUpperBound (T.UNIT, t) = T.UNIT
    | leastUpperBound (t, T.UNIT) = T.UNIT
    | leastUpperBound (T.NIL, T.RECORD(lst, ref1)) = T.RECORD(lst, ref1)
    | leastUpperBound (T.RECORD(lst, ref1), T.NIL) = T.RECORD(lst, ref1)
    | leastUpperBound (T.INT, T.INT) = T.INT
    | leastUpperBound (T.STRING, T.STRING) = T.STRING
    | leastUpperBound (T.NIL, T.NIL) = T.NIL
    | leastUpperBound (T.ARRAY(t1, ref1), T.ARRAY(t2, ref2)) = if ref1 = ref2
      then T.ARRAY(t1, ref1)
      else T.UNIT
    | leastUpperBound (T.RECORD(lst1, ref1), T.RECORD(lst2, ref2)) = if ref1 = ref2
      then T.RECORD(lst1, ref1)
      else T.UNIT
    | leastUpperBound (t1, t2) = T.UNIT

  (* skip past all the NAMES *)
  fun actual_ty (T.NAME(symbol, ref(SOME(t)))) = actual_ty  t
    | actual_ty other_ty = other_ty

  fun getTyFromSym(tenv: E.ty S.table, (name, pos):S.symbol) =
      case S.look(tenv, (name, pos)) of SOME (ty) => ty
                                      | NONE => ((error pos ("Undefined Type: " ^ name)); T.IMPOSSIBILITY)


  fun checkInt({exp, ty}, pos) = if isSubTy(ty, T.INT) then () else error pos ((T.name ty) ^ " is not a subtype of INT")


  fun checkSameType({exp=exp1, ty=ty1},{exp=exp2, ty=ty2}, pos) =
      if (isSubTy(actual_ty ty1, Types.INT) andalso isSubTy(actual_ty ty2, Types.INT)) then ()
      else
        if (isSubTy(actual_ty ty1, Types.STRING) andalso isSubTy(actual_ty ty2, Types.STRING)) then ()
        else error pos ("type " ^ (T.name (actual_ty ty1)) ^ " and type " ^ (T.name (actual_ty ty2)) ^" cannot be compared with <=, >=, >, <")

  fun checkEqual({exp=exp1, ty=T.UNIT},{exp=exp2, ty=_}, pos) = error pos "unit type can not be compared"
    | checkEqual({exp=exp1, ty=_},{exp=exp2, ty=T.UNIT}, pos) = error pos "unit type can not be compared"
    | checkEqual({exp=exp1, ty=T.NIL},{exp=exp2, ty=NIL}, pos) = error pos "nil can not be compared with nil"
    | checkEqual({exp=exp1, ty=ty1},{exp=exp2, ty=ty2}, pos)  = if (isSubTy(actual_ty ty1, actual_ty ty2) orelse isSubTy(actual_ty ty2, actual_ty ty1))
                                                                then ()
                                                                else error pos ("Type: " ^ T.name(actual_ty ty1) ^ " and " ^ T.name(actual_ty ty2) ^ " can not be compared")

  (*
transExp (venv * tenv) -> Absyn.exp -> expty
trexp: Absyn.exp -> expty
trvar: Absyn.var -> expty
 *)
  fun transExp(venv, tenv, in_loop:(unit option)) =
      let fun trexp (A.NilExp) = {exp=(), ty=T.NIL}
          | trexp (A.IntExp(int)) = {exp=(), ty=T.INT}
          | trexp (A.StringExp(string)) = {exp=(), ty=T.STRING}
          | trexp (A.VarExp(var)) = trvar var
          (* math operators *)
          | trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.MinusOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.TimesOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.DivideOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          (* comparison operators*)
          | trexp (A.OpExp{left, oper=A.GeOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.GtOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.LeOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.LtOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.EqOp, right, pos}) =
            (checkEqual(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
            (checkEqual(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          (*boolean operator*)
          (*if expression*)
          | trexp (A.IfExp({test=test_exp, then'=then_exp, else'=NONE, pos=pos'})) =
            let val {exp=_, ty=test_ty} = trexp(test_exp)
                val () = if isSubTy(actual_ty test_ty, T.INT) then ()
                         else error pos' ("If condition: type " ^ (T.name test_ty) ^ " is not a subtype of INT")
                val {exp=_, ty=then_ty} = trexp(then_exp)
                (* then_exp must evaluate to no value *)
                val () = if isSubTy(actual_ty then_ty, T.UNIT) andalso isSubTy(T.UNIT, actual_ty then_ty) then ()
                         else error pos' ("Then expression should be UNIT type rather than " ^ T.name(actual_ty then_ty))
            in
              {exp=(), ty=T.UNIT} (* if expression with no else, returns no value *)
            end
          | trexp (A.IfExp({test=test_exp, then'=then_exp, else'=SOME(else_exp), pos=pos'})) =
            let val {exp=_, ty=test_ty} = trexp(test_exp)
                val () = if isSubTy(actual_ty test_ty, T.INT) then ()
                         else error pos' ("If condition: type " ^ (T.name (actual_ty test_ty)) ^ " is not a subtype of INT")
                val {exp=_, ty=then_ty} = trexp(then_exp)
                val {exp=_, ty=else_ty} = trexp(else_exp)
                val rt = actual_ty(leastUpperBound(actual_ty then_ty, actual_ty else_ty))
            in
              {exp=(), ty=rt}
            end
          (* Record *)
          | trexp (A.RecordExp({fields, typ, pos})) = (
            case S.look(tenv, typ) of SOME(record_ty) => (
              case actual_ty record_ty of T.RECORD(results, unique) => (
                let
                    fun checkFieldTy([], []) = ()
		      | checkFieldTy(expfiles, []) = error pos "Extra fields for the record"
		      | checkFieldTy([], results) = error pos "Lack fileds for the record"
                      | checkFieldTy(expfield::l1, result::l2) =
                    let
                      val (sym, exp, pos) = expfield
                      val (name, name_ty) = result
                      fun checkName(sym, name) =
                        if S.name sym = S.name name then ()
                        else (error pos ("Record field names don't match: " ^ S.name sym ^ " with " ^ S.name name))
                      fun checkType(exp, name_ty) =
                        if isSubTy(actual_ty(#ty(trexp exp)), actual_ty name_ty) then ()
                        else (error pos ("Record: Type " ^ T.name(#ty(trexp exp)) ^ " is not a subtype of " ^ T.name(actual_ty name_ty)))
                    in
                      checkName(sym, name);
                      checkType(exp, name_ty);
                      checkFieldTy(l1, l2)
                    end
                in
                  if List.length(fields) = List.length(results)
                  then (checkFieldTy(fields, results); {exp=(), ty=T.RECORD(results, unique)})
                  else (error pos ("Record fields lengths don't match."); {exp=(), ty=T.IMPOSSIBILITY})
                end
              )
              | _ => (error pos ("Record type is undefined."); {exp=(), ty=T.IMPOSSIBILITY})
            )
            | _ => (error pos ("Record type is undefined."); {exp=(), ty=T.IMPOSSIBILITY})
          )
          (* Array *)
          | trexp (A.ArrayExp({typ, size, init, pos})) = (
              checkInt(trexp size, pos);
              case S.look(tenv, typ) of SOME(array_ty) => (
                case actual_ty array_ty of T.ARRAY(name_ty, unique) => (
                  if isSubTy(actual_ty(#ty(trexp init)), actual_ty name_ty) then ({exp=(), ty=T.ARRAY(actual_ty name_ty, unique)})
                  else (error pos ("Array types don't match."); {exp=(), ty=T.IMPOSSIBILITY})
                )
                | _ => (error pos ("Array type is undefined."); {exp=(), ty=T.IMPOSSIBILITY})
              )
              | _ => (error pos ("Array type is undefined."); {exp=(), ty=T.IMPOSSIBILITY})
            )
          (*Assign*)
          | trexp (A.AssignExp{var, exp, pos}) =
            let val vartype = trvar var
                val exptype = trexp exp
            in
              (*check if the type of exp is a subtype of var*)
              if (isSubTy(actual_ty(#ty(exptype)) , actual_ty(#ty(vartype)))) then ({exp=(), ty=T.UNIT})
              else (error pos "assignment type mismatch"; {exp=(), ty=T.UNIT})
            end
          (* call exp *)
          | trexp (A.CallExp{func=name, args=exp_lst, pos=pos'}) =
            let
              fun checkParams(typ_lst, rt) =
                  let
                    fun helper([], []) = {exp=(), ty=(actual_ty rt)} (* rt is the return type of the function *)
                      | helper((exp_a::exp_l), [])  = (error pos' "Too many args"; {exp=(), ty=T.IMPOSSIBILITY})
                      | helper([], (typ_a::typ_l))  = (error pos' "Too few args"; {exp=(), ty=T.IMPOSSIBILITY})
                      | helper((exp_a::exp_l), (typ_a::typ_l)) =
                        let val {exp=_, ty=exp_ty} = trexp(exp_a)
                        in
                          if isSubTy(actual_ty exp_ty, actual_ty typ_a) then helper(exp_l, typ_l)
                          else (error pos' ("Arg type does not match: " ^ (T.name exp_ty) ^ " isn't a subtype of " ^ (T.name typ_a) ); {exp=(), ty=T.IMPOSSIBILITY})
                        end
                  in
                    helper(exp_lst, typ_lst)
                  end

            in
              case S.look(venv, name) of SOME(E.FunEntry{formals=typ_lst, result=rt}) => checkParams(typ_lst, rt)
                                       | _ => ((error pos' ("Function " ^ (S.name name) ^ " is not defined")); {exp=(), ty=T.IMPOSSIBILITY})


            end

          (* let expression *)
          | trexp (A.LetExp{decs,body,pos}) =
            let
              val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs)
            in
              transExp(venv', tenv', in_loop) body (* break may occur in let body *)
            end
          | trexp (A.SeqExp(explst)) =
            let fun checkExprLst [] = {exp=(), ty= T.UNIT}
                | checkExprLst [(exp, pos)] = trexp exp
                | checkExprLst ((exp,pos)::l) = (trexp exp; checkExprLst l)
            in
              checkExprLst explst
            end
	  | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
	    let
              val () = checkInt(trexp lo, pos)
              val () = checkInt(trexp hi, pos)
              val venv' = S.enter(venv, var, E.VarEntry{ty=T.INT})
              val {exp=body_exp, ty=body_ty} = transExp(venv', tenv, SOME ()) body (* body is inside loop *)
              val () = if isSubTy(actual_ty(body_ty), T.UNIT) andalso isSubTy(T.UNIT,actual_ty(body_ty))
                       then () else (error pos "body of for loop should have UNIT as return value")
	    in
              {exp=(),ty=T.UNIT}
	    end
	  | trexp (A.WhileExp{test, body, pos}) =
            let
              val () = checkInt(trexp test, pos)
              val {exp=body_exp, ty=body_ty} = transExp(venv, tenv, SOME ()) body (* body is inside loop *)
              val () = if isSubTy(actual_ty body_ty, T.UNIT) andalso isSubTy(T.UNIT, actual_ty body_ty)
                       then ()
                       else (error pos ("body of while loop should have UNIT as return value, actual return " ^ T.name(actual_ty body_ty)))
            in
              {exp=(),ty=T.UNIT}
            end
	  | trexp (A.BreakExp(pos)) =
            let val () = case in_loop of NONE => error pos "not in a loop!"
                                       | SOME(_) => ()
            in {exp=(), ty=T.UNIT} end

        and trvar (A.SimpleVar(id,pos)) = (* check var binding exist : id *)
            (case S.look(venv,id) of
                SOME(E.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
              | SOME(E.FunEntry{formals, result}) =>
                (error pos ("var " ^ (S.name id) ^ " should be a variable rather than a func");
                  {exp=(), ty=T.IMPOSSIBILITY})
              | NONE =>
                (error pos ("undefined variable " ^ S.name id); {exp=(), ty=T.INT}))
          | trvar (A.FieldVar(v,sym,pos)) = (* check v.sym type *)
            let
              val v_ty = actual_ty(#ty (trvar v))
              fun getSymType([],sym,pos) = (error pos ("Symbol " ^ (S.name sym) ^ " wasn't found in the record"); {exp=(), ty=T.IMPOSSIBILITY})
                | getSymType((symbol, sym_ty)::l,sym,pos) =
                  if S.name symbol = S.name sym
                  then {exp=(), ty=actual_ty sym_ty}
                  else getSymType(l,sym,pos)
            in
              case v_ty of T.RECORD(fields_list,unique) => getSymType(fields_list,sym,pos)
              | _ => (error pos ("None record type cannot find a field"); {exp=(), ty=T.IMPOSSIBILITY})
            end
          | trvar (A.SubscriptVar(v,exp,pos)) = (* check v[exp] type *)
            let
              val v_ty = actual_ty(#ty (trvar v))
              val () = checkInt(trexp exp, pos)
            in
              case v_ty of T.ARRAY(array_ty, _) => {exp=(), ty=actual_ty array_ty}
              |  _ => (error pos ("None array type cannot be subscripted"); {exp=(), ty=T.IMPOSSIBILITY})
            end
      in
        trexp
      end
  and transDec (venv, tenv, []) = {venv = venv, tenv = tenv}
    | transDec (venv, tenv, decs) =
          (* var dec with type not specified *)
      let fun trdec(A.VarDec{name, escape, typ=NONE, init, pos}, {venv, tenv}) = (* var x := exp *)
              let val {exp, ty} = transExp(venv, tenv, NONE) init (* NONE -> new dec does not in loop *)
              in
                (* var x := nil is not allowed *)
                case ty of T.NIL => (error pos "NIL can not assign to var whose type is not determined";
                                     {venv=S.enter(venv, name, E.VarEntry{ty=T.IMPOSSIBILITY}), tenv=tenv})
                         | _ => {venv=S.enter(venv, name, E.VarEntry{ty=ty}), tenv=tenv}
              end
            (* var dec with type specified *)
            | trdec(A.VarDec{name, escape, typ=SOME(symbol, pos1), init, pos=pos2}, {venv, tenv})  =
              let
                val {exp, ty} = transExp(venv, tenv, NONE) init (* NONE -> new dec does not in loop *)
                val var_ty = actual_ty(transTy(tenv, A.NameTy(symbol, pos1)))
                val ty = actual_ty(ty)
              in
                if not (isSubTy(ty, var_ty)) then error pos2 (T.name(ty) ^ " is not a subtype of " ^ T.name(var_ty)) else ();
                {venv=S.enter(venv, name, E.VarEntry{ty=var_ty}), tenv=tenv}
              end
            (* typedecs *)
            | trdec(A.TypeDec(typedecs), {venv, tenv}) =
              let
                fun putHeaders(cur_tydec, tenv) = (* put all the headers in tenv -> tenv' *)
                    let val {name, ty, pos} = cur_tydec
                    in S.enter(tenv, name, T.NAME(name, ref NONE)) end
                fun processBodies(cur_tydec, tenv) =  (* process all the bodies in tenv' *)
                    let val {name, ty, pos} = cur_tydec
                    in (* assignments to ref variables *)
                      case S.look(tenv, name) of SOME(T.NAME(namety, unique)) => (unique := SOME(transTy(tenv, ty)); tenv)
                                               | _ => (error pos ("Undefined type " ^ S.name name); tenv)
                    end
                fun detectIllegalCycles([], tenv, typelist) = ()
                  | detectIllegalCycles(cur_tydec::l, tenv, typelist) = (* detect illegal cycles in type declarations *)
                    let
                      val {name, ty, pos} = cur_tydec
                    in
                      case S.look(tenv, name) of SOME(T.NAME(namety, unique)) => (
                         case !unique of SOME(T.NAME(mutual_namety, mutual_unique)) => (
                            if List.exists (fn cur_ty => S.name cur_ty = S.name mutual_namety) typelist
                            then error pos ("There's a illegal cycle in type declaration. ")
                            else detectIllegalCycles(l, tenv, namety::typelist)
                          )
                                       | _ => detectIllegalCycles(l, tenv, typelist)
                       )
                      | _ => (error pos ("Undefined type " ^ S.name name))
                    end
                val tenv' = foldl putHeaders tenv typedecs
                val complete_tenv = foldl processBodies tenv' typedecs
              in
                detectIllegalCycles(typedecs, complete_tenv, []);
                {venv=venv, tenv=complete_tenv}
              end

            | trdec (A.FunctionDec(fundecs), {venv, tenv}) =
              let
                (* enter each funcDec's signature (name, arg types) into venv *)
                fun enterFunc(fundec:A.fundec, venv) =
                    let val {name=name', params=fields, result=result', body=_, pos=pos'} = fundec
                        val formals' = foldr (fn (field, ans) => (actual_ty (getTyFromSym(tenv, (#typ field))))::ans) [] fields
                        val result_type = case result' of SOME(sym, pos1) => actual_ty(getTyFromSym(tenv, sym))
                                                         | NONE => T.UNIT (*func does not specify return type is a procedure*)
                        val entry = E.FunEntry{formals=formals', result=result_type}
                    in
                      S.enter(venv, name', entry)
                    end
                (* new venv contains all the signature of consecutive funcs*)
                val venv' = foldl enterFunc venv fundecs
                (* Parse the body of a func *)
                fun parseBody ({name=name', params=params', result=result', body=body', pos=pos'}:A.fundec) =
                    let
                      fun putParamInVenv(param:A.field, ans_venv) =
                          let val param_name = (#name param)
                              val param_ty = actual_ty(getTyFromSym(tenv, (#typ param)))
                              val param_var = E.VarEntry({ty=param_ty})
                          in
                            S.enter(ans_venv, param_name, param_var)
                          end

                      (* put all the params in this func into venv *)
                      val func_venv = foldr putParamInVenv venv' params'
                      val {exp=body_exp, ty=body_rt} = transExp(func_venv, tenv, NONE) body' (* NONE -> new fundec, not in loop *)
                      val rt = case result' of SOME(sym, pos1) => actual_ty(getTyFromSym(tenv, sym))
                                             | NONE => T.UNIT (* func does not specify return type is a procedure *)
                    in
                      if isSubTy(actual_ty body_rt, actual_ty rt) then ()
                      else error pos' ("Function return: type "^ (T.name(actual_ty body_rt)) ^ " is not a subtype of type " ^ (T.name(actual_ty rt)))
                    end
              in
                map parseBody fundecs;
                {venv=venv', tenv=tenv}
              end

      in
        foldl trdec {venv=venv, tenv=tenv} decs
      end

  and transTy (tenv, ty) =
      case ty of A.NameTy(symbol, pos) =>
                 (case S.look(tenv, symbol) of SOME(name_ty) => name_ty
                                             | NONE => (error pos ("Undefined type " ^ S.name symbol); T.IMPOSSIBILITY))
               | A.RecordTy(fields_list) => (
                 let
                   fun getFieldType(curr_field, result) =
                       let
                         val {name, escape, typ, pos} = curr_field
                       in
                         case S.look(tenv, typ) of SOME(name_ty) => (name, actual_ty(name_ty))::result
                                                 | NONE => (error pos ("Undefined type " ^ S.name typ); (name, T.UNIT)::result)
                       end
                   val results = foldr getFieldType [] fields_list
                 in
                   T.RECORD(results, ref ())
                 end
               )
               | A.ArrayTy(symbol, pos) => (
                 case S.look(tenv, symbol) of SOME(name_ty) => T.ARRAY(actual_ty(name_ty), ref ())
                                            | NONE => (error pos ("Undefined type " ^ S.name symbol); T.ARRAY(T.UNIT, ref ()))
               )


  fun transProg(exp:A.exp):unit = (transExp (E.base_venv, E.base_tenv, NONE) (exp);())
  (* NONE -> initially no loop *)

end




