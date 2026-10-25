package testUtils;

import java.util.List;

import core.E;
import core.OtherPackages;
import tools.SourceOracle;

public final class DbgBlock{
  static OtherPackages err(){ return FearlessTestBase.otherErr(); }

  public static List<E.Literal> all(){ return all; }

  public static SourceOracle dbgMiniBase(){
    return SourceOracle.debugBuilder()
      .put("_rank_base000.fear", baseHead)
      .put("baseBody.fear", baseBody)
      .build();
  }

  static String baseHead= "";










































































public static String _baseBody= "Sealed:{}";
public static String baseBody= """
Sealed:{}
CaptureFree: {}
FileLog: CaptureFree{ .name: Str; }
InMemoryLog[T]: CaptureFree{ .name: Str; }
Main: CaptureFree{ .main: Void }
InfoMain: CaptureFree{ .main: Void }
SystemAttenuator: CaptureFree{ #: Void }
Final[M]: {}
Named: Final[".name"]{ read .name: Str -> Nope!; }
DataRead: CaptureFree, Named{}
DataEdit: DataRead{}
OpenWith[I,E]: {}
Shortcut[I,E]: {}
WidenTo[T]:{}
BaseId[T1:*,T2]: CaptureFree{ #(x: T1): T2 }
BaseContainer[T1:*]: Sealed{
  read .as[T2](f: BaseId[read/imm T1,T2]): BaseContainer[T2] -> Nope!;
  imm .as[T2](f: BaseId[imm T1,T2]): BaseContainer[T2] -> Nope!;
  }
MList[E:*]: BaseContainer[E]{
  read .as[T2](f: BaseId[read/imm E,T2]): MList[T2] -> Nope!;
  imm .as[T2](f: BaseId[imm E,T2]): MList[T2] -> Nope!;
  .get: imm E -> Nope!;
  }
Todo: { ![R:**]: R -> Todo!;  }


Void:Sealed{}
F[R:**]: { read #: R }
F[A:**,R:**]: { read #(a: A): R }
F[A:**, B:**, R:**]: { read #(a: A, b: B): R }
F[A:**, B:**, C:**, R:**]: { read #(a: A, b: B, c: C): R }
F[A:**, B:**, C:**, D:**, R:**]: { read #(a: A, b: B, c: C, d: D): R }

MF[R:**]: { mut #: R }
MF[A:**,R:**]: { mut #(a: A): R }
MF[A:**, B:**, R:**]: { mut #(a: A, b: B): R }
MF[A:**, B:**, C:**, R:**]: { mut #(a: A, b: B, c: C): R }
MF[A:**, B:**, C:**, D:**, R:**]: { mut #(a: A, b: B, c: C, d: D): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, A31:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30, a31: A31): R }
MF[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, A31:**, A32:**, R:**]: { mut #(a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30, a31: A31, a32: A32): R }
Destruct: Sealed {
  #[A:**, R:**](a: A, f: mut MF[A, R]): R -> f#a;
  #[A:**, B:**, R:**](a: A, b: B, f: mut MF[A, B, R]): R -> f#(a, b);
  #[A:**, B:**, C:**, R:**](a: A, b: B, c: C, f: mut MF[A, B, C, R]): R -> f#(a, b, c);
  #[A:**, B:**, C:**, D:**, R:**](a: A, b: B, c: C, d: D, f: mut MF[A, B, C, D, R]): R -> f#(a, b, c, d);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, f: mut MF[A1, A2, A3, A4, A5, R]): R -> f#(a1, a2, a3, a4, a5);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, f: mut MF[A1, A2, A3, A4, A5, A6, R]): R -> f#(a1, a2, a3, a4, a5, a6);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, f: mut MF[A1, A2, A3, A4, A5, A6, A7, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, A31:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30, a31: A31, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31);
  #[A1:**, A2:**, A3:**, A4:**, A5:**, A6:**, A7:**, A8:**, A9:**, A10:**, A11:**, A12:**, A13:**, A14:**, A15:**, A16:**, A17:**, A18:**, A19:**, A20:**, A21:**, A22:**, A23:**, A24:**, A25:**, A26:**, A27:**, A28:**, A29:**, A30:**, A31:**, A32:**, R:**](a1: A1, a2: A2, a3: A3, a4: A4, a5: A5, a6: A6, a7: A7, a8: A8, a9: A9, a10: A10, a11: A11, a12: A12, a13: A13, a14: A14, a15: A15, a16: A16, a17: A17, a18: A18, a19: A19, a20: A20, a21: A21, a22: A22, a23: A23, a24: A24, a25: A25, a26: A26, a27: A27, a28: A28, a29: A29, a30: A30, a31: A31, a32: A32, f: mut MF[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, R]): R -> f#(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32);
  }
Nope:{![T:**]:T->Nope!}
Num:Sealed,WidenTo[Num]{ +(Num):Num->Nope!; *(Num):Num->Nope! }
Nat:Sealed,WidenTo[Nat]{ +(Nat):Nat->Nope!; *(Nat):Nat->Nope! }
Int:Sealed,WidenTo[Int]{ +(Int):Int->Nope!; *(Int):Int->Nope! }
Str:Sealed,WidenTo[Str]{}
Float:Sealed,WidenTo[Float]{}

Zero:Nat{}
One:Nat{}
Two:Nat{}
Three:Nat{}
Four:Nat{}
Five:Nat{}
Six:Nat{}
Seven:Nat{}
Eight:Nat{}
Nine:Nat{}
Ten:Nat{}

ToStr:{ read .str: Str }
ToUStr:{ read .uStr: UStr }

UStr:Sealed,WidenTo[UStr]{}

BoolMatch[R:**]:{
  mut .true: R;
  mut .false: R;
  }
Bool: Sealed,WidenTo[Bool]{
  .and(b: Bool): Bool;
  &&(b: mut MF[Bool]): Bool;
  &(b: Bool): Bool -> this.and(b);
  .or(b: Bool): Bool;
  |(b: Bool): Bool -> this.or(b);
  ||(b: mut MF[Bool]): Bool;
  .not: Bool;
  .if[R:**](f: mut ThenElse[R]): R;
  ?[R:**](f: mut ThenElse[R]): R -> this.if(f);
  .match[R](m: mut BoolMatch[R]): R -> this?{.then->m.true; .else->m.false};
  }
True: Bool{
  .and(b) -> b;
  &&(b) -> b#;
  .or(b) -> this;
  ||(b) -> this;
  .not -> False;
  .if(f) -> f.then;
  }
False: Bool{
  .and(b) -> this;
  &&(b) -> this;
  .or(b) -> b;
  ||(b) -> b#;
  .not -> True;
  .if(f) -> f.else;
  }
ThenElse[R:**]: { mut .then: R; mut .else: R; }

ReturnStmt[R:iso,imm,mut,read]: {mut #: R}
Condition: ReturnStmt[Bool]{}
LoopBody[R:*]: ReturnStmt[mut ControlFlow[R]]{}
Continuation[T:*,C:*,R:*]: {mut #(x: T, self: C): R}
ControlFlow: {
  .continue: mut ControlFlow[Void] -> mut ControlFlowContinue: ControlFlow[Void]{.match(m) -> m.continue};
  .break: mut ControlFlow[Void] -> mut ControlFlowBreak: ControlFlow[Void]{.match(m) -> m.break};
  .continueWith[T:*]: mut ControlFlow[T] ->  mut ControlFlowContinue[T:*]: ControlFlow[T]{.match(m) -> m.continue};
  .breakWith[T:*]: mut ControlFlow[T] -> mut ControlFlowBreak[T:*]: ControlFlow[T]{.match(m) -> m.break};
  .return[T:*](returnValue: T): mut ControlFlow[T] -> mut ControlFlowReturn[T:*]: ControlFlow[T]{
    .match(m) -> m.return(returnValue);
    mut .value: T -> returnValue;
    };
  }
ControlFlow[T:*]: {
  mut .match[R:*](m: mut ControlFlowMatch[T,R]): R -> m.continue;
  }
ControlFlowMatch[T:*,R:*]: {
  mut .continue: R;
  mut .break: R;
  mut .return(returnValue: T): R;
  }
Block: Sealed{
  #[R:*]: mut Block[R] -> {};
  #[X:**](x: X): Void -> {};
  #[X:**, R:**](_: X, res: R): R -> res;
  #[X1:**, X2:**, R:**](_: X1, _: X2, res: R): R -> res;
  #[X1:**, X2:**, X3:**, R:**](_: X1, _: X2, _: X3, res: R): R -> res;
  #[X1:**, X2:**, X3:**, X4:**, R:**](_: X1, _: X2, _: X3, _: X4, res: R): R -> res;
  }
Block[R:*]: Sealed,WidenTo[Block[R]]{
  mut .done: Void -> {};
  mut .return(a: mut ReturnStmt[R]): R -> a#;
  mut .do(r: mut ReturnStmt[Void]): mut Block[R] -> this._do(r#);
  mut ._do(v: Void): mut Block[R] -> this;
  mut .let[X:*](
    x: mut ReturnStmt[X],
    cont: mut Continuation[X, mut Block[R], R]
    ): R ->
      cont#(x#, this);
  mut .openIso[X:iso,imm,mut,read](
    x: iso X,
    cont: mut Continuation[mut X, mut Block[R], R]
    ): R ->
      cont#(x, this);
  mut .if(p: mut Condition): mut BlockIf[R] -> p# ? {
    .then -> { 't
      .return(a) -> _DecidedBlock#(a#);
      .do(r) -> t._do[](r#);
        mut ._do(v: Void): mut Block[R] -> this;
      };
    .else -> {
      .return(_) -> this;
      .do(_) -> this;
      };
    };
  mut .loop(body: mut LoopBody[R]): mut Block[R] -> body#.match{
    .continue -> this.loop(body);
    .break -> this;
    .return(rv) -> _DecidedBlock#rv;
    };
  }
BlockIf[R:*]:{
  mut .return(a: mut ReturnStmt[R]): mut Block[R];
  mut .do(r: mut ReturnStmt[Void]): mut Block[R];
  }
_DecidedBlock:{
  #[R:*](res: R): mut Block[R] -> { 'self
    .return(_) -> res;
    .do(_) -> self;
    .let(_, _) -> res;
    .openIso(_, _) -> res;
    .if(_) -> {
      .return(_) -> self;
      .do(_) -> self;
      };
  .loop(_) -> self;
  }
}
Opt[E:*]: _Opt[E] {
  .match m    -> m.empty;
  }
_Opt[E:*]: {
  mut  .match[R:**](mut OptMatch[E, R]): R;
  read .match[R:**](mut OptMatch[read/imm E, R]): R;
  imm  .match[R:**](mut OptMatch[imm E, R]): R;
  }
Opts: {
  #[E:*](x: E): mut Opt[E] -> { .match m -> m.some(x) };
  }
OptMatch[E:*,R:**]: {
  mut .some(E): R;
  mut .empty: R;
  }
""";
  static final List<E.Literal> all= FearlessTestBase.compileAll("base", dbgMiniBase(), err());
}