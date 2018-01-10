
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition ___builtin_bswap : ident := 27%positive.
Definition ___builtin_bswap16 : ident := 29%positive.
Definition ___builtin_bswap32 : ident := 28%positive.
Definition ___builtin_clz : ident := 30%positive.
Definition ___builtin_clzl : ident := 31%positive.
Definition ___builtin_clzll : ident := 32%positive.
Definition ___builtin_ctz : ident := 33%positive.
Definition ___builtin_ctzl : ident := 34%positive.
Definition ___builtin_ctzll : ident := 35%positive.
Definition ___builtin_debug : ident := 48%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition ___builtin_fmadd : ident := 39%positive.
Definition ___builtin_fmax : ident := 37%positive.
Definition ___builtin_fmin : ident := 38%positive.
Definition ___builtin_fmsub : ident := 40%positive.
Definition ___builtin_fnmadd : ident := 41%positive.
Definition ___builtin_fnmsub : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 36%positive.
Definition ___builtin_membar : ident := 5%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_nop : ident := 47%positive.
Definition ___builtin_read16_reversed : ident := 43%positive.
Definition ___builtin_read32_reversed : ident := 44%positive.
Definition ___builtin_va_arg : ident := 7%positive.
Definition ___builtin_va_copy : ident := 8%positive.
Definition ___builtin_va_end : ident := 9%positive.
Definition ___builtin_va_start : ident := 6%positive.
Definition ___builtin_write16_reversed : ident := 45%positive.
Definition ___builtin_write32_reversed : ident := 46%positive.
Definition ___compcert_va_composite : ident := 13%positive.
Definition ___compcert_va_float64 : ident := 12%positive.
Definition ___compcert_va_int32 : ident := 10%positive.
Definition ___compcert_va_int64 : ident := 11%positive.
Definition ___i64_dtos : ident := 14%positive.
Definition ___i64_dtou : ident := 15%positive.
Definition ___i64_sar : ident := 26%positive.
Definition ___i64_sdiv : ident := 20%positive.
Definition ___i64_shl : ident := 24%positive.
Definition ___i64_shr : ident := 25%positive.
Definition ___i64_smod : ident := 22%positive.
Definition ___i64_stod : ident := 16%positive.
Definition ___i64_stof : ident := 18%positive.
Definition ___i64_udiv : ident := 21%positive.
Definition ___i64_umod : ident := 23%positive.
Definition ___i64_utod : ident := 17%positive.
Definition ___i64_utof : ident := 19%positive.
Definition _avg : ident := 66%positive.
Definition _c : ident := 56%positive.
Definition _c0 : ident := 60%positive.
Definition _c1 : ident := 62%positive.
Definition _main : ident := 69%positive.
Definition _n : ident := 55%positive.
Definition _od_add : ident := 51%positive.
Definition _od_add_avg : ident := 53%positive.
Definition _od_fdct_2 : ident := 68%positive.
Definition _od_mul : ident := 58%positive.
Definition _od_rot2 : ident := 64%positive.
Definition _od_rotate_pi4_kernel : ident := 67%positive.
Definition _od_sub : ident := 52%positive.
Definition _od_sub_avg : ident := 54%positive.
Definition _p0 : ident := 49%positive.
Definition _p1 : ident := 50%positive.
Definition _q : ident := 57%positive.
Definition _q0 : ident := 61%positive.
Definition _q1 : ident := 63%positive.
Definition _t : ident := 59%positive.
Definition _type : ident := 65%positive.
Definition _t'1 : ident := 70%positive.
Definition _t'10 : ident := 79%positive.
Definition _t'11 : ident := 80%positive.
Definition _t'12 : ident := 81%positive.
Definition _t'13 : ident := 82%positive.
Definition _t'14 : ident := 83%positive.
Definition _t'15 : ident := 84%positive.
Definition _t'16 : ident := 85%positive.
Definition _t'17 : ident := 86%positive.
Definition _t'18 : ident := 87%positive.
Definition _t'19 : ident := 88%positive.
Definition _t'2 : ident := 71%positive.
Definition _t'20 : ident := 89%positive.
Definition _t'21 : ident := 90%positive.
Definition _t'22 : ident := 91%positive.
Definition _t'3 : ident := 72%positive.
Definition _t'4 : ident := 73%positive.
Definition _t'5 : ident := 74%positive.
Definition _t'6 : ident := 75%positive.
Definition _t'7 : ident := 76%positive.
Definition _t'8 : ident := 77%positive.
Definition _t'9 : ident := 78%positive.

Definition f_od_add := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p0, tint) :: (_p1, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _p0 tint) (Etempvar _p1 tint) tint)))
|}.

Definition f_od_sub := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p0, tint) :: (_p1, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Osub (Etempvar _p0 tint) (Etempvar _p1 tint) tint)))
|}.

Definition f_od_add_avg := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p0, tint) :: (_p1, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _od_add (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
    ((Etempvar _p0 tint) :: (Etempvar _p1 tint) :: nil))
  (Sreturn (Some (Ebinop Oshr
                   (Ebinop Oadd (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
                   (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_od_sub_avg := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p0, tint) :: (_p1, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _od_sub (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
    ((Etempvar _p0 tint) :: (Etempvar _p1 tint) :: nil))
  (Sreturn (Some (Ebinop Oshr
                   (Ebinop Oadd (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
                   (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_od_mul := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: (_c, tint) :: (_q, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oshr
                 (Ebinop Oadd
                   (Ebinop Omul (Etempvar _n tint) (Etempvar _c tint) tint)
                   (Ebinop Oshr
                     (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                       (Etempvar _q tint) tint)
                     (Econst_int (Int.repr 1) tint) tint) tint)
                 (Etempvar _q tint) tint)))
|}.

Definition f_od_rot2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p0, (tptr tint)) :: (_p1, (tptr tint)) :: (_t, tint) ::
                (_c0, tint) :: (_q0, tint) :: (_c1, tint) :: (_q1, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _p0 (tptr tint)) tint))
      (Scall (Some _t'1)
        (Evar _od_mul (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil)))
                        tint cc_default))
        ((Etempvar _t'3 tint) :: (Etempvar _c0 tint) ::
         (Etempvar _q0 tint) :: nil)))
    (Sassign (Ederef (Etempvar _p1 (tptr tint)) tint) (Etempvar _t'1 tint)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _od_mul (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil)))
                      tint cc_default))
      ((Etempvar _t tint) :: (Etempvar _c1 tint) :: (Etempvar _q1 tint) ::
       nil))
    (Sassign (Ederef (Etempvar _p0 (tptr tint)) tint) (Etempvar _t'2 tint))))
|}.

Definition f_od_rotate_pi4_kernel := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p0, (tptr tint)) :: (_p1, (tptr tint)) :: (_c0, tint) ::
                (_q0, tint) :: (_c1, tint) :: (_q1, tint) :: (_type, tint) ::
                (_avg, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'22, tint) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _type tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sifthenelse (Etempvar _avg tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'21 (Ederef (Etempvar _p1 (tptr tint)) tint))
              (Ssequence
                (Sset _t'22 (Ederef (Etempvar _p0 (tptr tint)) tint))
                (Scall (Some _t'3)
                  (Evar _od_add_avg (Tfunction (Tcons tint (Tcons tint Tnil))
                                      tint cc_default))
                  ((Etempvar _t'21 tint) :: (Etempvar _t'22 tint) :: nil))))
            (Sset _t'2 (Ecast (Etempvar _t'3 tint) tint)))
          (Sset _t'1 (Ecast (Etempvar _t'2 tint) tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'19 (Ederef (Etempvar _p1 (tptr tint)) tint))
              (Ssequence
                (Sset _t'20 (Ederef (Etempvar _p0 (tptr tint)) tint))
                (Scall (Some _t'4)
                  (Evar _od_add (Tfunction (Tcons tint (Tcons tint Tnil))
                                  tint cc_default))
                  ((Etempvar _t'19 tint) :: (Etempvar _t'20 tint) :: nil))))
            (Sset _t'2 (Ecast (Etempvar _t'4 tint) tint)))
          (Sset _t'1 (Ecast (Etempvar _t'2 tint) tint))))
      (Sifthenelse (Etempvar _avg tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'17 (Ederef (Etempvar _p1 (tptr tint)) tint))
              (Ssequence
                (Sset _t'18 (Ederef (Etempvar _p0 (tptr tint)) tint))
                (Scall (Some _t'6)
                  (Evar _od_sub_avg (Tfunction (Tcons tint (Tcons tint Tnil))
                                      tint cc_default))
                  ((Etempvar _t'17 tint) :: (Etempvar _t'18 tint) :: nil))))
            (Sset _t'5 (Ecast (Etempvar _t'6 tint) tint)))
          (Sset _t'1 (Ecast (Etempvar _t'5 tint) tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'15 (Ederef (Etempvar _p1 (tptr tint)) tint))
              (Ssequence
                (Sset _t'16 (Ederef (Etempvar _p0 (tptr tint)) tint))
                (Scall (Some _t'7)
                  (Evar _od_sub (Tfunction (Tcons tint (Tcons tint Tnil))
                                  tint cc_default))
                  ((Etempvar _t'15 tint) :: (Etempvar _t'16 tint) :: nil))))
            (Sset _t'5 (Ecast (Etempvar _t'7 tint) tint)))
          (Sset _t'1 (Ecast (Etempvar _t'5 tint) tint)))))
    (Sset _t (Etempvar _t'1 tint)))
  (Ssequence
    (Scall None
      (Evar _od_rot2 (Tfunction
                       (Tcons (tptr tint)
                         (Tcons (tptr tint)
                           (Tcons tint
                             (Tcons tint
                               (Tcons tint (Tcons tint (Tcons tint Tnil)))))))
                       tvoid cc_default))
      ((Etempvar _p0 (tptr tint)) :: (Etempvar _p1 (tptr tint)) ::
       (Etempvar _t tint) :: (Etempvar _c0 tint) :: (Etempvar _q0 tint) ::
       (Etempvar _c1 tint) :: (Etempvar _q1 tint) :: nil))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _type tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'13 (Ederef (Etempvar _p1 (tptr tint)) tint))
            (Ssequence
              (Sset _t'14 (Ederef (Etempvar _p0 (tptr tint)) tint))
              (Scall (Some _t'9)
                (Evar _od_sub (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                                cc_default))
                ((Etempvar _t'13 tint) :: (Etempvar _t'14 tint) :: nil))))
          (Sset _t'8 (Ecast (Etempvar _t'9 tint) tint)))
        (Ssequence
          (Ssequence
            (Sset _t'11 (Ederef (Etempvar _p1 (tptr tint)) tint))
            (Ssequence
              (Sset _t'12 (Ederef (Etempvar _p0 (tptr tint)) tint))
              (Scall (Some _t'10)
                (Evar _od_add (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                                cc_default))
                ((Etempvar _t'11 tint) :: (Etempvar _t'12 tint) :: nil))))
          (Sset _t'8 (Ecast (Etempvar _t'10 tint) tint))))
      (Sassign (Ederef (Etempvar _p1 (tptr tint)) tint) (Etempvar _t'8 tint)))))
|}.

Definition f_od_fdct_2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p0, (tptr tint)) :: (_p1, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _od_rotate_pi4_kernel (Tfunction
                                (Tcons (tptr tint)
                                  (Tcons (tptr tint)
                                    (Tcons tint
                                      (Tcons tint
                                        (Tcons tint
                                          (Tcons tint
                                            (Tcons tint (Tcons tint Tnil))))))))
                                tvoid cc_default))
  ((Etempvar _p1 (tptr tint)) :: (Etempvar _p0 (tptr tint)) ::
   (Econst_int (Int.repr 11585) tint) :: (Econst_int (Int.repr 13) tint) ::
   (Econst_int (Int.repr 11585) tint) :: (Econst_int (Int.repr 13) tint) ::
   (Econst_int (Int.repr 1) tint) ::
   (Eunop Onotbool (Econst_int (Int.repr 0) tint) tint) :: nil))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_od_add, Gfun(Internal f_od_add)) :: (_od_sub, Gfun(Internal f_od_sub)) ::
 (_od_add_avg, Gfun(Internal f_od_add_avg)) ::
 (_od_sub_avg, Gfun(Internal f_od_sub_avg)) ::
 (_od_mul, Gfun(Internal f_od_mul)) ::
 (_od_rot2, Gfun(Internal f_od_rot2)) ::
 (_od_rotate_pi4_kernel, Gfun(Internal f_od_rotate_pi4_kernel)) ::
 (_od_fdct_2, Gfun(Internal f_od_fdct_2)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _od_fdct_2 :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

