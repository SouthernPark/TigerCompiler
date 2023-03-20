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
  structure Tr = Translate
  type venv = Env.enventry S.table
  type tenv = T.ty S.table
  type expty = {exp: Tr.exp, ty: T.ty}
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

  (* zip([1,2], [3,4]) => [(1,3), (2,4)]*)
  fun zip ([], []) = []
    | zip ([], l) = []
    | zip (l, []) = []
    | zip ((a1::l1), (a2::l2)) = (a1, a2) :: zip(l1, l2)

  fun checkInt(ty, pos) = if isSubTy(ty, T.INT) then () else error pos ((T.name ty) ^ " is not a subtype of INT")


  (*string compare and int compare*)
  fun checkSameType(ty1, ty2, pos) =
      if (isSubTy(actual_ty ty1, Types.INT) andalso isSubTy(actual_ty ty2, Types.INT)) then ()
      else
        if (isSubTy(actual_ty ty1, Types.STRING) andalso isSubTy(actual_ty ty2, Types.STRING)) then ()
        else error pos ("type " ^ (T.name (actual_ty ty1)) ^ " and type " ^ (T.name (actual_ty ty2)) ^" cannot be compared with <=, >=, >, <")

  (**)
  fun checkEqual(T.UNIT, _, pos) = error pos "unit type can not be compared"
    | checkEqual(_, T.UNIT, pos) = error pos "unit type can not be compared"
    | checkEqual(T.NIL, T.NIL, pos) = error pos "nil can not be compared with nil"
    | checkEqual(ty1, ty2, pos)  = if (isSubTy(actual_ty ty1, actual_ty ty2) orelse isSubTy(actual_ty ty2, actual_ty ty1))
                                   then ()
                                   else error pos ("Type: " ^ T.name(actual_ty ty1) ^ " and " ^ T.name(actual_ty ty2) ^ " can not be compared")

  fun transExp(venv, tenv, loop_end_label:(Temp.label option), level:Tr.level) =
      let fun trexp (A.NilExp) = {exp=Tr.transNIL(), ty=T.NIL}
          | trexp (A.IntExp(int)) = {exp=Tr.transINT(int), ty=T.INT}
          | trexp (A.StringExp(string)) = {exp=Tr.TODO, ty=T.STRING}
          | trexp (A.VarExp(var)) = trvar var
          | trexp (A.OpExp{left, oper, right, pos}) =
            let val {exp=left_exp, ty=left_ty} = trexp left
                val {exp=right_exp, ty=right_ty} = trexp right
                fun math_operator() = (checkInt(left_ty, pos); checkInt(right_ty, pos); {exp=Tr.transBINOP(left_exp, right_exp, oper), ty=T.INT})
                fun compare_operator() = (checkSameType(left_ty, right_ty, pos); {exp=Tr.transBINOP(left_exp, right_exp, oper), ty=T.INT})
                fun eq_operator() = (checkEqual(left_ty, right_ty, pos); {exp=Tr.transBINOP(left_exp, right_exp, oper), ty=T.INT})
            in
              case oper of A.PlusOp => math_operator()
                         | A.MinusOp => math_operator()
                         | A.TimesOp => math_operator()
                         | A.DivideOp => math_operator()
                         | A.GeOp => compare_operator()
                         | A.GtOp => compare_operator()
                         | A.LeOp => compare_operator()
                         | A.LtOp => compare_operator()
                         | A.EqOp => eq_operator()
                         | A.NeqOp => eq_operator()
            end
          (*if expression*)
          | trexp (A.IfExp({test=test_exp, then'=then_exp, else'=NONE, pos=pos'})) =
            let val {exp=_, ty=test_ty} = trexp(test_exp)
                val () = if isSubTy(actual_ty test_ty, T.INT) then ()
                         else error pos' ("If condition: type " ^ (T.name test_ty) ^ " is not a subtype of INT")
                val {exp=_, ty=then_ty} = trexp(then_exp)
                (* then_exp must evaluate to no value *)
                val () = if isSubTy(actual_ty then_ty, T.UNIT) then ()
                         else error pos' (T.name(actual_ty then_ty) ^ " is not a subtype of UNIT.")
            in
              {exp=Tr.transINT(0), ty=T.UNIT} (* if expression with no else, returns no value *)
            end
          | trexp (A.IfExp({test=test_exp, then'=then_exp, else'=SOME(else_exp), pos=pos'})) =
            let val {exp=test_exp', ty=test_ty} = trexp(test_exp)
                val () = if isSubTy(actual_ty test_ty, T.INT) then ()
                         else error pos' ("If condition: type " ^ (T.name (actual_ty test_ty)) ^ " is not a subtype of INT")
                val {exp=then_exp', ty=then_ty} = trexp(then_exp)
                val {exp=else_exp', ty=else_ty} = trexp(else_exp)
                val rt = actual_ty(leastUpperBound(actual_ty then_ty, actual_ty else_ty))
            in
              {exp=Tr.transIF(test_exp', then_exp', else_exp'), ty=rt}
            end
          (* Record *)
          | trexp (A.RecordExp({fields, typ, pos})) = (
            case S.look(tenv, typ) of SOME(record_ty) => (
              case actual_ty record_ty of T.RECORD(results, unique) => (
                let
                    fun checkFieldTy([], []) = ()
		      | checkFieldTy(fields, []) = error pos "Extra fields for the record"
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
                    fun getExps([], explist) = explist
                      | getExps((field::l), explist) =
                          let
                            val (sym, exp, pos) = field
                          in
                            getExps(l, explist@[#exp(trexp exp)])
                          end
                    val exps = getExps(fields, [])
                in
                  if List.length(fields) = List.length(results)
                  then (checkFieldTy(fields, results); {exp=Tr.transRECORD(exps), ty=T.RECORD(results, unique)})
                  else (error pos ("Record fields lengths don't match."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
                end
              )
              | _ => (error pos ("Record type is undefined."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
            )
            | _ => (error pos ("Record type is undefined."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
          )
          (* Array *)
          | trexp (A.ArrayExp({typ, size, init, pos})) =
            let val {exp=size_val, ty=size_ty} = trexp size
                val {exp=init_val, ty=init_ty} = trexp init
                val () = checkInt(size_ty, pos);
            in

              case S.look(tenv, typ) of SOME(array_ty) => (
                 case actual_ty array_ty of T.ARRAY(name_ty, unique) => (
                    if isSubTy(actual_ty init_ty, actual_ty name_ty) then ({exp=Tr.transARRAY(size_val, init_val), ty=T.ARRAY(actual_ty name_ty, unique)})
                    else (error pos ("Array types don't match."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
                  )
                                          | _ => (error pos ("Array type is undefined."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
               )
                                      | _ => (error pos ("Array type is undefined."); {exp=Tr.ERROREXP, ty=T.IMPOSSIBILITY})
            end
          (*Assign*)
          | trexp (A.AssignExp{var, exp, pos}) =
            let val {ty=vartype, exp=varMem} = trvar var
                val {ty=exptype, exp=expVal} = trexp exp
            in
              (*check if the type of exp is a subtype of var*)
              if isSubTy(actual_ty exptype, actual_ty vartype) then ({exp=Tr.transASSIGN(varMem, expVal), ty=T.UNIT})
              else (error pos "assignment type mismatch"; {exp=Tr.ERROREXP, ty=T.UNIT})
            end
          (* call exp *)
          | trexp (A.CallExp{func=func_name, args=exp_lst, pos=pos'}) =
            let
              fun checkParams(typ_lst, rt) =
                  let
                    fun helper([], []) = ([], (actual_ty rt)) (* rt is the return type of the function *)
                      | helper((exp_a::exp_l), [])  = (error pos' "Too many args"; ([], T.IMPOSSIBILITY))
                      | helper([], (typ_a::typ_l))  = (error pos' "Too few args"; ([], T.IMPOSSIBILITY))
                      | helper((exp_a::exp_l), (typ_a::typ_l)) =
                        let
                          val {exp=cur_arg_exp, ty=exp_ty} = trexp(exp_a)
                          val (rest_arg_exps, rt) = if isSubTy(actual_ty exp_ty, actual_ty typ_a) then helper(exp_l, typ_l)
                                                          else (error pos' ("Arg type does not match: " ^ (T.name exp_ty) ^ " isn't a subtype of " ^ (T.name typ_a) ); ([], T.IMPOSSIBILITY))
                        in
                          (cur_arg_exp::rest_arg_exps, rt)
                        end
                  in
                    helper(exp_lst, typ_lst)
                  end
            in
              case S.look(venv, func_name) of SOME(E.FunEntry{level=funLevel, label=funLabel,formals=typ_lst, result=rt}) =>
                                              let val (arg_exps, rt) = checkParams(typ_lst, rt)
                                              in
                                                {exp=Tr.transCall(arg_exps, level, funLevel, funLabel), ty=rt}
                                              end
                                            | _ => ((error pos' ("Function " ^ (S.name func_name) ^ " is not defined")); {exp=raise ErrorMsg.Error, ty=T.IMPOSSIBILITY})
            end

          (* let expression *)
          | trexp (A.LetExp{decs,body,pos}) =
            let
              val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs, loop_end_label, level)
            in
              transExp(venv', tenv', loop_end_label, level) body (* break may occur in let body *)
            end
          | trexp (A.SeqExp(explst)) =
            let fun checkExprLst [] = {exp=Tr.TODO, ty= T.UNIT}
                | checkExprLst [(exp, pos)] = trexp exp
                | checkExprLst ((exp,pos)::l) = (trexp exp; checkExprLst l)
            in
              checkExprLst explst
            end
	  | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
	    let
              val {exp=lo_val, ty=low_ty} = trexp lo
              val {exp=hi_val, ty=hi_ty} = trexp hi
              val () = checkInt(low_ty, pos)
              val () = checkInt(hi_ty, pos)
              val venv' = S.enter(venv, var, E.VarEntry{access=Tr.allocLocal level (!escape), ty=T.INT})
              val {exp=body_exp, ty=body_ty} = transExp(venv', tenv, SOME(Temp.newlabel()), level) body
              val () = if isSubTy(actual_ty(body_ty), T.UNIT)
                       then () else (error pos (T.name (actual_ty body_ty) ^ " is not a subtype of UNIT."))
	    in
              {exp=Tr.TODO,ty=T.UNIT}
	    end
	  | trexp (A.WhileExp{test, body, pos}) =
            let
              val {exp=test_val, ty=test_ty} = trexp test
              val () = checkInt(test_ty, pos)
              val {exp=body_exp, ty=body_ty} = transExp(venv, tenv, SOME(Temp.newlabel()), level) body
              val () = if isSubTy(actual_ty body_ty, T.UNIT)
                       then ()
                       else (error pos (T.name(actual_ty body_ty) ^ " is not a subtype of UNIT"))
            in
              {exp=Tr.TODO,ty=T.UNIT}
            end
	  | trexp (A.BreakExp(pos)) =
            let val break_end_label = case loop_end_label of NONE => (error pos "not in a loop!"; Temp.newlabel())
                                              | SOME(l) => l
            in {exp=Tr.transBREAK(break_end_label), ty=T.IMPOSSIBILITY} end

        and trvar (A.SimpleVar(id,pos)) = (* check var binding exist : id *)
            (case S.look(venv,id) of
                SOME(E.VarEntry{access, ty}) => {exp=Tr.transSIMPLEVAR(access, level), ty=actual_ty ty}
              | SOME(E.FunEntry{level=funLevel, label=funLabel, formals, result}) =>
                (error pos ("var " ^ (S.name id) ^ " should be a variable rather than a func");
                  {exp=Tr.Ex(Tree.CONST(0)), ty=T.IMPOSSIBILITY})
              | NONE =>
                (error pos ("undefined variable " ^ S.name id); {exp=Tr.Ex(Tree.CONST(0)), ty=T.INT}))
          | trvar (A.FieldVar(v,sym,pos)) = (* check v.sym type *)
            let
              val v_ty = actual_ty(#ty (trvar v))
              fun getSymType([],sym,pos) = (error pos ("Symbol " ^ (S.name sym) ^ " wasn't found in the record"); {exp=Tr.TODO, ty=T.IMPOSSIBILITY})
                | getSymType((symbol, sym_ty)::l,sym,pos) =
                  if S.name symbol = S.name sym
                  then {exp=Tr.TODO, ty=actual_ty sym_ty}
                  else getSymType(l,sym,pos)
            in
              case v_ty of T.RECORD(fields_list,unique) => getSymType(fields_list,sym,pos)
              | _ => (error pos ("None record type cannot find a field"); {exp=Tr.TODO, ty=T.IMPOSSIBILITY})
            end
          | trvar (A.SubscriptVar(v,exp,pos)) = (* check v[exp] type *)
            let
              val v_ty = actual_ty(#ty (trvar v))
              val {exp=sub_val, ty=sub_ty} = trexp exp;
              val () = checkInt(sub_ty, pos)
            in
              case v_ty of T.ARRAY(array_ty, _) => {exp=Tr.TODO, ty=actual_ty array_ty}
              |  _ => (error pos ("None array type cannot be subscripted"); {exp=Tr.TODO, ty=T.IMPOSSIBILITY})
            end
      in
        trexp
      end
  and transDec (venv, tenv, [], loop_end_label:(Temp.label option), level:Tr.level) = {venv = venv, tenv = tenv}
    | transDec (venv, tenv, decs, loop_end_label:(Temp.label option), level:Tr.level) =
          (* var dec with type not specified *)
      let fun trdec(A.VarDec{name, escape, typ=NONE, init, pos}, {venv, tenv}) = (* var x := exp *)
              let
                val {exp, ty} = transExp(venv, tenv, loop_end_label, level) init (*var dec does not change loop level *)
                val access = Tr.allocLocal level (!escape)
              in
                (* var x := nil is not allowed *)
                case ty of T.NIL => (error pos "NIL can not assign to var whose type is not determined";
                                     {venv=S.enter(venv, name, E.VarEntry{access=access, ty=T.IMPOSSIBILITY}), tenv=tenv})
                         | _ => {venv=S.enter(venv, name, E.VarEntry{access=access, ty=ty}), tenv=tenv}
              end
            (* var dec with type specified *)
            | trdec(A.VarDec{name, escape, typ=SOME(symbol, pos1), init, pos=pos2}, {venv, tenv})  =
              let
                val {exp, ty} = transExp(venv, tenv, loop_end_label, level) init (*var dec does not change loop level *)
                val var_ty = actual_ty(transTy(tenv, A.NameTy(symbol, pos1)))
                val ty = actual_ty(ty)
              in
                if not (isSubTy(ty, var_ty)) then error pos2 (T.name(ty) ^ " is not a subtype of " ^ T.name(var_ty)) else ();
                {venv=S.enter(venv, name, E.VarEntry{access=Tr.allocLocal level (!escape), ty=var_ty}), tenv=tenv}
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
                fun detectDuplicateNames([], typelist) = ()
                  | detectDuplicateNames(cur_tydec::l, typelist) =
                    let
                      val {name, ty, pos} = cur_tydec
                    in
                      if List.exists (fn cur_ty => S.name cur_ty = S.name name) typelist
                      then error pos ("There's a duplicate type name in this mutual tydec groups. ")
                      else detectDuplicateNames(l, name::typelist)
                    end
                val tenv' = foldl putHeaders tenv typedecs
                val complete_tenv = foldl processBodies tenv' typedecs
              in
                detectDuplicateNames(typedecs, []);
                detectIllegalCycles(typedecs, complete_tenv, []);
                {venv=venv, tenv=complete_tenv}
              end

            | trdec (A.FunctionDec(fundecs), {venv, tenv}) =
              let
                (* enter each funcDec's signature (name, arg types) into venv *)
                fun addFuncSig(fundec:A.fundec, venv) =
                    let val {name=name', params=fields, result=result', body=_, pos=pos'} = fundec
                        val formals' = foldr (fn (field, ans) => (actual_ty (getTyFromSym(tenv, (#typ field))))::ans) [] fields
                        val result_type = case result' of SOME(sym, pos1) => actual_ty(getTyFromSym(tenv, sym))
                                                         | NONE => T.UNIT (*func does not specify return type is a procedure*)
                        val formals_escape = foldr (fn (field, ans) => (!(#escape field)::ans)) [] fields
                        (* fun entry's level is the same as cur level *)
                        val funLabel = Temp.newlabel() (* address for the function's machine code *)
                        val funLevel = Tr.newLevel({parent=level, name=funLabel, formals=formals_escape}) (*deeper level*)
                        val entry = E.FunEntry{level=funLevel, label=funLabel, formals=formals', result=result_type}
                    in
                      S.enter(venv, name', entry)
                    end

                val venv' = foldl addFuncSig venv fundecs

                (* Parse the body of a func *)
                fun parseBody ({name=name', params=params', result=result', body=body', pos=pos'}:A.fundec) =
                    let
                      val {level=func_level, label=_, formals=_, result=rt} =
                          case S.look(venv, name') of
                              SOME(E.FunEntry(r)) => r
                            | _ => (error pos' ("Function: " ^ (S.name name') ^ " does not exist."); raise ErrorMsg.Error)

                      val param_access_lst = Tr.formals func_level
                      val param_zip = zip(params', param_access_lst)
                      fun putParamInVenv((param:A.field, access:Tr.access), ans_venv) =
                          let val param_name = (#name param)
                              val param_ty = actual_ty(getTyFromSym(tenv, (#typ param)))
                              val param_var = E.VarEntry({access=access, ty=param_ty})
                          in
                            S.enter(ans_venv, param_name, param_var)
                          end

                      (* put all the params in this func into venv *)
                      val func_venv = foldr putParamInVenv venv' param_zip
                      (* translate func body *)
                      val {exp=body_exp, ty=body_rt} = transExp(func_venv, tenv, NONE, func_level) body' (* NONE -> new fundec, not in loop *)

                    in
                      if isSubTy(actual_ty body_rt, actual_ty rt) then ()
                      else error pos' ("Function return: type "^ (T.name(actual_ty body_rt)) ^ " is not a subtype of type " ^ (T.name(actual_ty rt)))
                    end
                fun detectDuplicateNames([], funlist) = ()
                  | detectDuplicateNames(cur_fundec::l, funlist) =
                    let
                      val {name=name', params=fields, result=result', body=_, pos=pos'} = cur_fundec
                    in
                      if List.exists (fn cur_fun => S.name cur_fun = S.name name') funlist
                      then error pos' ("There's a duplicate fun name in this mutual fundec groups. ")
                      else detectDuplicateNames(l, name'::funlist)
                    end
              in
                detectDuplicateNames(fundecs, []);
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


  fun transProg(exp:A.exp):unit =
      let
        val tig_main_level = Tr.newLevel({parent=Tr.outermost, name=Temp.newlabel(),formals=[]})
      in
	  transExp (E.base_venv, E.base_tenv, NONE, tig_main_level) (exp);()
      end

  (* NONE -> initially no loop *)

end




