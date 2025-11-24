package typeSystem;

public class Kinding {

}


/*
  Bs|- T1:RCs1 ... Bs|-Tn:RCsn
  D[X1:RCs1..Xn:RCn]:_ in Decs
--------------------------
  Bs|-RC D[T1..Tn] : RC

  X in dom(Bs)
------------------------
  Bs|- RC X : RC

----------------------
  Bs|- X:Bs(X)
  
  Bs|- T:RCs
------------------------
  Bs|- T:RCs,_
  
---------------------------
  Bs|- read/imm X:read,imm
  
  Bs|- X:iso,imm
-----------------------------
  Bs|- read/imm X:imm
 
  Bs|-X:mut,mutH,read,readH
 ----------------------------
  Bs|- read/imm X:read
*/