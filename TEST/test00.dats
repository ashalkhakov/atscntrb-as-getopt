#include
"share/atspre_staload.hats"

(* ****** ****** *)

staload "libats/SATS/dynarray.sats"
staload _(*anon*) = "libats/DATS/dynarray.dats"
//
staload
_ = "prelude/DATS/reference.dats"
//
#include "./../mylibies.hats"
//
#staload $GETOPT // opening it
//
#include "./../mylibies_link.hats"
//
(* ****** ****** *)
//
typedef testE = @{i=size_t, k=string, v=string}
//
fun
fprint_testE (out: FILEref, e: testE): void =
   fprint!(out, "i=[", e.i, "], k = [", e.k, "], v = [", e.v, "]")
//
implement
fprint_val<testE> (out, e) = fprint_testE (out, e)
//
(* ****** ****** *)
//
extern
fun
test1 (): void
implement
test1 () = let
//
  var lst = dynarray_make_nil<testE>((i2sz)10)
  prval pf_lst = view@ lst
  var count: size_t
  val () = count := g0ofg1 ((i2sz)0)
  prval pf_count = view@ count
//
  implement
  arg$match<void> (env, index, oi, key, value) = let
    prval (pf_lst, fpf) = decode($vcopyenv_v(pf_lst))
    prval (pf_count, fpf_count) = decode($vcopyenv_v(pf_count))
    val () = dynarray_insert_at_exn<testE> (lst, count, @{i= index, k= oi.lname, v= value})
    val () = count := succ(count)
    prval () = fpf (pf_lst)
    prval () = fpf_count (pf_count)
  in
  end
//
  implement
  arg$error<void> (env, arg, ix, ecode) = println!("got error; argument [", arg, "], index = ", ix)
//
  #define NOPTS 3
  var opts = @[optinfo](
    @{lname="output", sname='o', arity=OArequired(), help="specify the output file"},
    @{lname="warning", sname='W', arity=OArequired(), help="warning level"},
    @{lname="help", sname='h', arity=OAnull(), help="display help"}
  ) (* end of [var] *)
//
  var args0 = @[string]("--output=out.ppm", "--help", "-ofoo.bar", "-o", "baz.qux", "--warning", "WARN", "test arg")
  var cur: size_t
  val () = cur := (i2sz)0
  var env: void = ()
  val-GOnext() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOstop() = getopt_env<void> (env, (i2sz)8, args0, cur, opts, (i2sz)NOPTS)
//
  prval () = view@ (lst) := pf_lst
  prval () = view@ (count) := pf_count
  val out = stdout_ref
  val () = fprint_dynarray (out, lst)
  val () = fprintln!(out)
//
  val- @{i= _(*0*), k="output", v="out.ppm"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*2*), k="help", v=_} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*0*), k="output", v="foo.bar"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*0*), k="output", v="baz.qux"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*1*), k="warning", v="WARN"} = dynarray_takeout_at_exn (lst, (i2sz)0)
// 
  val-true = (cur = (i2sz)7)
//
  val () = dynarray_free (lst)
//
in
end // end of [test1]
//
(* ****** ****** *)
//
extern
fun
test2 {n:int} (size_t(n), !argv(n)): void

local

  #define NOPTS 4
  var opts = @[optinfo](
    @{lname="output", sname='\000', arity=OArequired(), help="specify the output file"},
    @{lname="warning", sname='W', arity=OArequired(), help="warning level"},
    @{lname="push", sname='\000', arity=OAoptional(), help="optional argument"},
    @{lname="help", sname='h', arity=OAnull(), help="display help"}
  ) (* end of [var] *)
  val p_opts = addr@opts
  prval pf_opts = view@opts
  val the_opts = ref_make_viewptr {@[optinfo][NOPTS]} (pf_opts | p_opts)

  fun
  get_help (arg0: string): void = {
    val (pf_opts, fpf | p_opts) = $effmask_ref (ref_vtakeout (the_opts))
    val () = getopt_help<> (arg0, !p_opts, (i2sz)NOPTS)
    prval () = fpf (pf_opts)
  } (* end of [get_help] *)

in // in of [local]

implement
test2 {n} (argc, argv) = let
//
  prval () = lemma_argv_param (argv)
  prval () = lemma_g1uint_param (argc)
  val-true = isgtz(argc)
//
  val arg0 = argv[0]
//
//
  implement
  arg$match<void> (env, index, oi, key, value) = let
  in
    if index = (i2sz)2(*help*) then get_help (arg0)
    else
    println!("match: optind=[", index, "], key = [", key, "], value = [", value, "]")
  end
//
  implement
  arg$error<void> (env, arg, ix, ecode) = println!("got error; argument [", arg, "], index = ", ix)
//
  implement
  getopt_all$rest<void> {n} (env, sz, arr) = {
    val () = println!("rest of args:")
    val () = fprint_array_size<string> (stdout_ref, arr, sz)
    val () = print_newline ()
    val () = println!("end of args")
  } (* end of [getopt_all$rest] *)
//
  val () =
    if :(argv: argv(n)) => argc < 2 then {
      val () = get_help (arg0)
    }
    else {
      val (pf_arr, pf_minus | p_arr) = argv_takeout_strarr (argv)
      val cur = (i2sz)1
      var env: void = ()
      val (pf_opts, fpf | p_opts) = $effmask_ref (ref_vtakeout (the_opts))
      val _ = getopt_all_env<void> (env, argc, !p_arr, cur, !p_opts, (i2sz)NOPTS)
      prval () = fpf (pf_opts)
      prval () = minus_v_addback (pf_minus, pf_arr | argv)
    } (* end of [val] *)
//
//
in
end // end of [test2]
//
end // end of [local]
//
(* ****** ****** *)
//
implement
main0 (argc, argv) = let
//
  val () = unit_test ()
//
  val () = println!("test1")
  val () = test1 ()
  val () = println!("test1 END")
//
  val () = println!("test2")
  val () = test2 ((i2sz)argc, argv)
  val () = println!("test2 END")
//
in
end
