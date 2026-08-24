package typeSystem;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import core.FearlessException;
import core.OtherPackages;
import main.FrontendLogicMain;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

public class PromotionMatrixTest extends testUtils.FearlessTestBase{
  static final List<String> rets= List.of("R","imm R","read R","mut R","readH R","mutH R","iso R","read/imm R");
  static final List<String> gRcs= List.of("imm","read","mut","iso","readH","mutH");
  static final List<String> recvs= List.of("imm","read","mut");
  static final List<String> bounds= List.of("imm","mut","read","imm,mut","*","**");
  static final OtherPackages base= OtherPackages.start(Map.of(), DbgBlock.all(), -1);
  static String src(String bound, String recv, String gRc, String ret){
    return "G[R:"+bound+"]: { "+recv+" .get: R }\n"
      +"C: { .m[R:"+bound+"](g: "+gRc+" G[R]): "+ret+" -> g.get; }\n";
  }
  static String cell(String bound, String recv, String gRc, String ret){
    var o= SourceOracle.debugBuilder().put(0,src(bound,recv,gRc,ret)).build();
    try{ new FrontendLogicMain().of("p",Map.of(), o.allFiles(), o, base); return "o"; }
    catch(FearlessException _){ return "e"; }
  }
  static String row(String bound, String recv, String gRc){
    return Join.of(rets.stream().map(ret->cell(bound,recv,gRc,ret)),String.format("  %-5s ",gRc),"","\n");
  }
  static String block(String bound, String recv){
    return "R:"+bound+" .get is "+recv+"\n"+Join.of(gRcs.stream().map(g->row(bound,recv,g)),"","","");
  }
  static String matrix(){
    return Join.of(rets,"cols: "," | ","\n\n")
      +bounds.stream().flatMap(b->recvs.stream().map(recv->block(b,recv))).collect(Collectors.joining("\n"));
  }
@Test void promotionMatrix(){ strCmp("""
cols: R | imm R | read R | mut R | readH R | mutH R | iso R | read/imm R

R:imm .get is imm
  imm   oooeoeeo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeeeee

R:imm .get is read
  imm   oooeoeeo
  read  oooeoeeo
  mut   oooeoeeo
  iso   oooeoeeo
  readH oooeoeeo
  mutH  oooeoeeo

R:imm .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oooeoeeo
  iso   oooeoeeo
  readH eeeeeeee
  mutH  oooeoeeo

R:mut .get is imm
  imm   oooooooo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooooooo
  readH eeeeeeee
  mutH  eeeeeeee

R:mut .get is read
  imm   oooooooo
  read  oeooooeo
  mut   oeooooeo
  iso   oooooooo
  readH eeeeooee
  mutH  eeeeooee

R:mut .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oeooooeo
  iso   oooooooo
  readH eeeeeeee
  mutH  eeeeooee

R:read .get is imm
  imm   oooeoeeo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeeeee

R:read .get is read
  imm   oooeoeeo
  read  oeoeoeeo
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeoeee
  mutH  eeeeoeee

R:read .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeoeee

R:imm,mut .get is imm
  imm   oooeoeeo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeeeee

R:imm,mut .get is read
  imm   oooeoeeo
  read  oeoeoeeo
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeoeee
  mutH  eeeeoeee

R:imm,mut .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeoeee

R:* .get is imm
  imm   oooeoeeo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeeeee

R:* .get is read
  imm   oooeoeeo
  read  oeoeoeeo
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeoeee
  mutH  eeeeoeee

R:* .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oeoeoeeo
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeoeee

R:** .get is imm
  imm   oooeoeeo
  read  eeeeeeee
  mut   eeeeeeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeeeee

R:** .get is read
  imm   oooeoeeo
  read  oeeeoeee
  mut   oeeeoeee
  iso   oooeoeeo
  readH eeeeoeee
  mutH  eeeeoeee

R:** .get is mut
  imm   eeeeeeee
  read  eeeeeeee
  mut   oeeeoeee
  iso   oooeoeeo
  readH eeeeeeee
  mutH  eeeeoeee
""",matrix()); }
}
