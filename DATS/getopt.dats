#include
"share/atspre_staload.hats"

staload UN =
"prelude/SATS/unsafe.sats"

staload "./../SATS/getopt.sats"

#define ATS_DYNLOADFLAG 0

extern
fun{}
string1_skip {n,i:int | i <= n} (string(n), size_t(i)): string(n-i)
implement
string1_skip<> (s, i) = let
  fun
  aux {n,i:nat | i <= n} (s: string(n), r: size_t(i)): string(n-i) =
    if r > (i2sz)0 then aux (string_tail(s), pred(r))
    else s
  // end of [aux]
  prval () = lemma_string_param (s)
  prval () = lemma_g1uint_param (i)
in
  aux (s, i)
end // end of [string1_skip]

datatype optknd =
  | OKeof of ()
  | OKparm of ()
  | OKshort of ()
  | OKlong of ()
  | OKerror of ()

fun
fprint_optknd (out: FILEref, ok: optknd): void =
case+ ok of
| OKeof () => fprint!(out, "OKeof()")
| OKparm () => fprint!(out, "OKparm()")
| OKshort () => fprint!(out, "OKshort()")
| OKlong () => fprint!(out, "OKlong()")
| OKerror () => fprint!(out, "OKerror()")

implement
fprint_val<optknd> (out, e) = fprint_optknd (out, e)

extern
fun{}
arg_get_optknd (string, &string? >> string): optknd

extern
fun{}
arg_get_param (
  arg: string, shortopt: bool
, key: &ptr? >> strptr(l)
, value: &string? >> opt (string, b)
): #[b:bool;l:addr | b && l > null || ~b && l == null] bool(b)

extern
fun{}
find_optinfo {m:int} (&(@[optinfo][m]), size_t(m), ok: optknd, arg: string): sizeLte(m)

(* ****** ****** *)

implement
arg_get_optknd<> (arg, res) = let
  val arg = (g1ofg0)arg
in
  if string_is_empty(arg) then (res := arg; OKparm)
  else begin
    if string_head(arg) = '-' then let
      val arg1 = string_tail(arg)
    in
      if string_is_empty(arg1) then (res := arg; OKparm)
      else
      if string_head(arg1) = '-' then let
        val arg2 = string_tail(arg1)
      in
        if string_is_empty(arg2) then (res := arg; OKeof)
        else (res := arg2; OKlong)
      end
      else (res := arg1; OKshort)
    end
    else (res := arg; OKparm)
  end
end // end of [arg_get_optknd]

(*
given either short or long arg,
we can say if it contains a "value" or not
- short args: W0<-the rest is the value
- long args: W=k<- anything following = is the value
*)
implement
arg_get_param<> (arg, shortopt, key, value) = let
  val arg = (g1ofg0)arg
in
  if shortopt then begin
    if string_is_empty(arg) then let
      val () = key := strptr_null ()
      prval () = opt_none{string}(value)
    in false end
    else let
      val tail = string_tail(arg)
    in
      if string_is_empty(tail) then let
        val () = key := strptr_null ()
        prval () = opt_none{string}(value)
      in false end
      else let
        val k = string_make_substring (arg, (i2sz)0, (i2sz)1)
        val () = key := strnptr2strptr(k)
        val-true = strptr_isnot_null (key)
        val () = value := tail
        prval () = opt_some{string}(value)
      in true end
    end // end of [string_is_empty]
  end
  else let // long option
    // find first '=' in arg
    val ix = string_index (arg, '=')
  in
    if ix = ~1 then let
      val () = key := strptr_null ()
      prval () = opt_none{string}(value)
    in false end
    else let
      val ix = g1int2uint_ssize_size (ix)
      val ix1 = succ(ix)
      val substr = string1_skip (arg, ix1)
      val () = value := substr
      val k = string_make_substring (arg, (i2sz)0, ix)
      val () = key := strnptr2strptr (k)
      val-true = strptr_isnot_null (key)
      prval () = opt_some{string}(value)
    in
      true
    end
  end
end // end of [arg_get_param]

implement
find_optinfo<> {m} (opts, optsz, ok, arg) = let
  val arg = (g1ofg0)arg
  prval () = lemma_array_param (opts)
in
  // let X be an optinfo taken from opts
  // if X matches arg
  case+ ok of
  | OKeof () => optsz
  | OKparm () => optsz
  | OKerror () => optsz
  | OKshort () =>
    if string_is_empty (arg) then optsz
    else let
      val c = string_head (arg)
      // look for sname=c in opts
      implement(env)
      array_iforeach$cont<optinfo><env>(i, x, env) =
        if x.sname = c then false(*stop*)
        else true
      implement(env)
      array_iforeach$fwork<optinfo><env>(i, x, env) = ()
    in
      array_iforeach (opts, optsz)
    end // end of [OKshort]
  | OKlong () =>
    if string_is_empty (arg) then optsz
    else let
      implement(env)
      array_iforeach$cont<optinfo><env>(i, x, env) =
        if x.lname = arg then false(*stop*)
        else true
      implement(env)
      array_iforeach$fwork<optinfo><env>(i, x, env) = ()
    in
      array_iforeach (opts, optsz)
    end // end of [OKshort]
end // end of [find_optinfo]

(* ****** ****** *)

extern
fun{env:vt@ype}
process_one_arg {n,n1,m:int | n1 < n} (
  env: &(env) >> _
, argc: size_t(n)
, argv: &(@[string][n])
, cur: &size_t(n1) >> size_t(n2)
, arg: string
, opts: &(@[optinfo][m])
, optsz: size_t(m)
, is_short: bool
): #[n2:int | n2 <= n] getopt_ret

implement{env}
process_one_arg {n,n1,m} (
  env
, argc, argv
, cur
, arg
, opts, optsz
, is_short
) = let
  // extract possible value (has value)
  var key: ptr
  var value: string
  val has_value = arg_get_param (arg, is_short, key, value)
  val ok = if is_short then OKshort() else OKlong()
(*
  val () = println!("process_one_arg: arg = [", arg, "], cur = [", cur, "], is_short: [", is_short, "]")
*)
in
  if :(key: ptr?, value: string?) => has_value then let
    // find optinfo for this arg
    val ix = find_optinfo (opts, optsz, ok, $UN.cast{string}(strptr2ptr(key)))
    prval () = opt_unsome{string}(value)
    val value1 = value
    prval () = topize{string}(value)
  in
    if ix = optsz then let
      val () = arg$error<env> (env, $UN.cast{string}(strptr2ptr(key)), cur, ERRunknown_argument())
      val () = strptr_free (key)
    in
      GOerr ()
    end
    else (
      case+ opts.[ix].arity of
      | OAnull () => let
          val () = arg$error<env> (env, $UN.cast{string}(strptr2ptr(key)), cur, ERRunexpected_param())
          val () = strptr_free (key)
        in
          GOerr ()
        end
      | _ => let // can consume this argument
        prval () = lemma_g1uint_param (ix)
        val () = arg$match<env> (env, ix, opts.[ix], opts.[ix].lname, value1)
        val () = strptr_free (key)
        val () = cur := succ(cur)
      in
        GOnext ()
      end)
  end
  else let // no value specified
    // find optinfo for this arg
    val ix = find_optinfo (opts, optsz, ok, arg)
    val () = strptr_free (key)
    prval () = opt_unnone{string}(value)
  in
    if ix = optsz then let
      val () = arg$error<env> (env, arg, cur, ERRunknown_argument())
    in
      GOerr ()
    end
    else let
      prval () = lemma_g1uint_param (ix)
    in
      case+ opts.[ix].arity of
      | OArequired () => let
        in
          if succ(cur) < argc then let
             val cur1 = succ(cur)
             // consume this argument
             val () = arg$match<env> (env, ix, opts.[ix], arg, argv.[cur1])
             val () = cur := succ(cur1)
          in
             GOnext ()
          end
          else let
            val () = arg$error<env> (env, arg, cur, ERRmissing_param())
          in
            GOerr ()
          end
        end
      | OAoptional () => let // not required, so...
          val cur1 = succ(cur)
        in
          if cur1 < argc then let
            // see if it is a param or arg
            val arg1 = argv.[cur1]
            var arg1' : string
            val optknd1 = arg_get_optknd (arg1, arg1')
            val arg1 = arg1
          in
            case+ optknd1 of
            | OKparm () => let        
                val () = arg$match<env> (env, ix, opts.[ix], arg, arg1)
                val () = cur := succ(cur1)
              in
                GOnext ()
              end // end of [OKparm]
            | _ => let // not a parameter
                val () = arg$match<env> (env, ix, opts.[ix], arg, "")
                val () = cur := succ(cur)
              in
                GOnext ()
              end // end of [OKparm]
          end // end of [if]
          else let // no parameter present
            val () = arg$match<env> (env, ix, opts.[ix], arg, "")
            val () = cur := succ(cur)
          in
            GOnext ()
          end // end of [else ...]
        end // end of [OAoptional]
      | OAnull () => let // no parameter is expected
          val () = arg$match<env> (env, ix, opts.[ix], arg, "")
          val () = cur := succ(cur)
        in
          GOnext ()
        end // end of [OKparm]
    end // end of [if ix = optsz]
  end // end of [if has_value]
end // end of [process_one_arg]

implement{env}
getopt_env {n,n1,m} (env, argc, argv, cur, opts, optsz) =
  if cur = argc then GOstop ()
  else let
    val arg0 = argv.[cur]
    // see if it is a param or arg
    var arg : string
    val optknd = arg_get_optknd (arg0, arg)
    val arg = arg
  in
    case+ optknd of
    | OKlong () => process_one_arg<env> (env, argc, argv, cur, arg, opts, optsz, false)
    | OKshort () => process_one_arg<env> (env, argc, argv, cur, arg, opts, optsz, true)
    | OKeof () => let
        val () =
          if cur < argc then {
            // consume the "--"
            val () = cur := succ(cur)
          } (* end of [val] *)
      in
        GOstop ()
      end // end of [OKeof]
    | OKparm () => GOstop ()
    | OKerror () => GOerr ()
  end // end of [getopt_env]

(* ****** ****** *)

implement{env}
getopt_all$rest {n} (env, sz, arr) = ()

implement{env}
getopt_all_env {n,n1,m} (env, argc, argv, cur, opts, optsz) = let
  prval () = lemma_g1uint_param (argc)
  prval () = lemma_g1uint_param (cur)
  prval () = lemma_g1uint_param (optsz)

  fun
  go_cont (i: getopt_ret): bool = case+ i of GOnext () => true | _ => false

  var i: size_t
  val () = i := cur
  var res: getopt_ret = GOnext ()
  val () =
    while* {i:nat | i <= n}
      (i: size_t(i), res: getopt_ret, env: env, argv: @[string][n], opts: @[optinfo][m]):
      (i: sizeLte(n), res: getopt_ret, env: env, argv: @[string][n], opts: @[optinfo][m]) =>
      (i < argc && go_cont (res)) (let
      val () = res := getopt_env<env> (env, argc, argv, i, opts, optsz)
      prval () = lemma_g1uint_param (i)
    in
    end) // end of [for]
  // now, extract some stuff here.. from the tail of the array

  fun
  getopt_all$rest_prf {n:int} {l:addr} (
    pf_arr: !array_v (string, l, n)
  | env: &(env) >> _, n: size_t(n), p_arr: ptr l
  ): void = getopt_all$rest<env> (env, n, !p_arr)

  val p_arr = addr@argv
  prval pf_arr = view@argv
  val i1 = i
  prval (pf1_arr, pf2_arr) = array_v_split_at {string} (pf_arr | i1)
  val p_arr = ptr1_add_guint<string> (p_arr, i1)
  
  val () = getopt_all$rest_prf (pf2_arr | env, argc-i1, p_arr)
  
  prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
  prval () = view@argv := pf_arr
in
  res
end // end of [getopt_all_env]

(* ****** ****** *)

implement{}
getopt_help {m} (arg0, opts, optsz) = let
//
  fun
  indent (out: FILEref, nspaces: int): void = {
    var i: int = 0
    val () = while (i < nspaces) (i := i + 1; fprint!(out, ' '))
  } (* end of [indent] *)
//
  // calculate max nspaces per every option
  var optheader: int = 0
  implement
  array_foreach$fwork<optinfo><int> (oi, env) = {
    var res: int = 0

    val has_sname = (oi.sname <> '\000')
    val () = res := res + 2

    val lname = (g1ofg0)oi.lname
    val has_lname = string_isnot_empty(lname)
    val () = res := res + 2

    val () =
      if has_lname then {
        val () = res := res + 2 + (sz2i)(string_length oi.lname) + 1
        val () = res := res + g0ofg1_int(case+ oi.arity of OAnull() => 0 | OArequired() => 4 | _ => 6)
      }
    val () = res := res + 2
    val () = env := max (env, res)
  } (* end of [array_foreach_env$fwork] *)
  val _ = array_foreach_env<optinfo><int> (opts, optsz, optheader)
//
  val optheader = optheader
//
  implement
  fprint_array$sep<> (out) = fprint_newline (out)
  implement
  fprint_ref<optinfo> (out, oi) = {
    // use up as many as you need, and pad the unused space
    var res : int = optheader
    val optname: string = g0ofg1_string(case+ oi.arity of OAnull() => "" | OArequired() => "ARG" | _ => "[ARG]")

    val () = indent (out, 2)

    val has_sname = (oi.sname <> '\000')
    val () =
      if has_sname then {
        val () = fprint!(out, "-", oi.sname)
      }
      else {
        val () = fprint!(out, "  ")
      }(* end of [val] *)
    val () = res := res - 2

    val lname = (g1ofg0)oi.lname
    val has_lname = string_isnot_empty(lname)
    val () =
      if has_sname && has_lname then {
        val () = fprint!(out, ", ")
      }
      else {
        val () = fprint!(out, "  ")
      }(* end of [val] *)
    val () = res := res - 2

    val () =
      if has_lname then {
        val () = fprint!(out, "--", oi.lname)
        val () = case+ oi.arity of OAnull () => () | _ => fprint!(out, "=", optname)
        val () = res := res - (2 + (sz2i)(string_length oi.lname) + 1)
        val () = res := res - g0ofg1_int(case+ oi.arity of OAnull() => 0 | OArequired() => 4 | _ => 6)
      }
      else {
      }(* end of [val] *)

    val () = indent (out, res)
    val () = fprint!(out, oi.help)
  }
  val () = fprintln!(stdout_ref, "usage: ", arg0, " [OPTION] arg...")
  val () = fprint_array_size<optinfo> (stdout_ref, opts, optsz)
  val () = fprintln!(stdout_ref)
in
end

(* ****** ****** *)

implement
unit_test<> () = {
//
// arg_get_optknd
val () = {
  val arg = "--"
  var res: string
  val-OKeof() = arg_get_optknd (arg, res)
  val-true = (res = "--")
}

val () = {
  val arg = "--help"
  var res: string
  val-OKlong() = arg_get_optknd (arg, res)
  val-true = (res = "help")
}

val () = {
  val arg = "-W"
  var res: string
  val-OKshort() = arg_get_optknd (arg, res)
  val-true = (res = "W")
}

val () = {
  val arg = "-W0"
  var res: string
  val-OKshort() = arg_get_optknd (arg, res)
  val-true = (res = "W0")
}

val () = {
  val arg = "-"
  var res: string
  val-OKparm() = arg_get_optknd (arg, res)
  val-true = (res = "-")
}

val () = {
  val arg = "hello"
  var res: string
  val-OKparm() = arg_get_optknd (arg, res)
  val-true = (res = "hello")
}
// end of [arg_get_optknd]

// arg_get_param
val () = {
  var k: strptr
  var res: string
  val-true = arg_get_param("W0", true, k, res)
  prval () = opt_unsome{string}(res)
  val-true = (k = "W")
  val-true = (res = "0")
  val () = strptr_free(k)
}
val () = {
  var k: strptr
  var res: string
  val-false = arg_get_param("W", true, k, res)
  prval () = opt_unnone{string}(res)
  prval () = strptr_free_null(k)
}
val () = {
  var k: strptr
  var res: string
  val-true = arg_get_param("output=file.o", false, k, res)
  prval () = opt_unsome{string}(res)
  val-true = (res = "file.o")
  val-true = (k = "output")
  val () = strptr_free(k)
}
val () = {
  var k: strptr
  var res: string
  val-true = arg_get_param("output=", false, k, res)
  prval () = opt_unsome{string}(res)
  val-true = (res = "")
  val-true = (k = "output")
  val () = strptr_free(k)
}
// end of [arg_get_param]

// find_optinfo
val () = {
  #define NOPTS 3
  var opts = @[optinfo](
    @{lname="output", sname='o', arity=OArequired(), help=""},
    @{lname="warning", sname='W', arity=OArequired(), help=""},
    @{lname="help", sname='h', arity=OAnull(), help=""}
  ) (* end of [var]*)
 
  val ix = find_optinfo (opts, (i2sz)NOPTS, OKshort(), "h")
  val-true = (ix = (i2sz)2)
 
  val ix = find_optinfo (opts, (i2sz)NOPTS, OKlong(), "help")
  val-true = (ix = (i2sz)2)

  val ix = find_optinfo (opts, (i2sz)NOPTS, OKshort(), "W")
  val-true = (ix = (i2sz)1)

  val ix = find_optinfo (opts, (i2sz)NOPTS, OKshort(), "v")
  val-true = (ix = NOPTS) // not found
}
// end of [find_optinfo]
//
} (* end of [unit_test] *)
