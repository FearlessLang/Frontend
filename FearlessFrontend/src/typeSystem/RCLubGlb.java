package typeSystem;

import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import fearlessParser.RC;
import static fearlessParser.RC.*;

import static java.util.EnumSet.of;

public class RCLubGlb{
  private static final EnumSet<RC> allRC= EnumSet.allOf(RC.class);
  private static final Map<Set<RC>, RC> lubMap= new HashMap<>();
  private static final Map<Set<RC>, RC> glbMap= new HashMap<>();
  public static final Set<Set<RC>> domain(){ return Collections.unmodifiableSet(lubMap.keySet()); }
  public static RC lub(EnumSet<RC> options){ return lubMap.get(options); }
  public static RC glb(EnumSet<RC> options){ return glbMap.get(options); }
  static boolean isUb(EnumSet<RC> options, RC ub){ return options.stream().allMatch(x -> ub.isSubType(x)); }
  static boolean isLb(EnumSet<RC> options,RC lb){ return options.stream().allMatch(x -> x.isSubType(lb)); }
  static boolean isLub(EnumSet<RC> options,RC lub){
    var isUb= isUb(options,lub);
    var isLowest= allRC.stream()
      .filter(RC -> isUb(options,RC))
      .allMatch(ub -> ub.isSubType(lub));
    return isUb && isLowest;
  }
  static boolean isGlb(EnumSet<RC> options,RC glb){
    var isLb= isLb(options,glb);
    var isGreatest= allRC.stream()
      .filter(RC -> isLb(options,RC))
      .allMatch(lb -> glb.isSubType(lb));    
    return isLb && isGreatest;
  }
  static void init(EnumSet<RC> options,RC lub,RC glb){
    var novel1= lubMap.put(options,lub);
    var novel2= glbMap.put(options, glb);
    assert novel1 == null && novel2 == null;
    assert isLub(options,lub) :"not lub: "+lub+" "+options;
    assert isGlb(options,glb) :"not glb: "+glb+" "+options;
    var otherLub= allRC.stream().filter(RC->RC!=lub).filter(RC->isLub(options,RC)).toList();
    assert otherLub.isEmpty() :"not unique Lub: "+otherLub;
    var otherGlb= allRC.stream().filter(RC->RC!=glb).filter(RC->isGlb(options,RC)).toList();
    assert otherGlb.isEmpty() :"not unique glb: "+otherGlb;
  }
  static {// RCs                  | LUB    | GLB
    init(of(iso),                   iso,     iso);
    init(of(imm),                   imm,     imm);
    init(of(mut),                   mut,     mut);
    init(of(mutH),                  mutH,    mutH);
    init(of(read),                  read,    read);
    init(of(readH),                 readH,   readH);

    init(of(iso,imm),               iso,     imm);
    init(of(iso,mut),               iso,     mut);
    init(of(iso, mutH),             iso,     mutH);
    init(of(iso, read),             iso,     read);
    init(of(iso, readH),            iso,     readH);
    init(of(imm, mut),              iso,     read);
    init(of(imm, mutH),             iso,     readH);
    init(of(imm, read),             imm,     read);
    init(of(imm, readH),            imm,     readH);
    init(of(mut, mutH),             mut,     mutH);
    init(of(mut, read),             mut,     read);
    init(of(mut, readH),            mut,     readH);
    init(of(mutH, read),            mut,     readH);
    init(of(mutH, readH),           mutH,    readH);
    init(of(read, readH),           read,    readH);

    init(of(iso, imm, mut),         iso,     read);
    init(of(iso, imm, mutH),        iso,     readH);
    init(of(iso, imm, read),        iso,     read);
    init(of(iso, imm, readH),       iso,     readH);
    init(of(iso, mut, mutH),        iso,     mutH);
    init(of(iso, mut, read),        iso,     read);
    init(of(iso, mut, readH),       iso,     readH);
    init(of(iso, mutH, read),       iso,     readH);
    init(of(iso, mutH, readH),      iso,     readH);
    init(of(iso, read, readH),      iso,     readH);
    init(of(imm, mut, mutH),        iso,     readH);
    init(of(imm, mut, read),        iso,     read);
    init(of(imm, mut, readH),       iso,     readH);
    init(of(imm, mutH, read),       iso,     readH);
    init(of(imm, mutH, readH),      iso,     readH);
    init(of(imm, read, readH),      imm,     readH);
    init(of(mut, mutH, read),       mut,     readH);
    init(of(mut, mutH, readH),      mut,     readH);
    init(of(mut, read, readH),      mut,     readH);
    init(of(mutH, read, readH),     mut,     readH);

    init(of(iso, imm, mut, mutH),   iso,     readH);
    init(of(iso, imm, mut, read),   iso,     read);
    init(of(iso, imm, mut, readH),  iso,     readH);
    init(of(iso, imm, mutH, read),  iso,     readH);
    init(of(iso, imm, mutH, readH), iso,     readH);
    init(of(iso, imm, read, readH), iso,     readH);
    init(of(iso, mut, mutH, read),  iso,     readH);
    init(of(iso, mut, mutH, readH), iso,     readH);
    init(of(iso, mut, read, readH), iso,     readH);
    init(of(iso, mutH, read, readH),iso,     readH);
    init(of(imm, mut, mutH, read),  iso,     readH);
    init(of(imm, mut, mutH, readH), iso,     readH);
    init(of(imm, mut, read, readH), iso,     readH);
    init(of(imm, mutH, read, readH),iso,     readH);
    init(of(mut, mutH, read, readH),mut,     readH);

    init(of(iso, imm, mut, mutH, read),       iso, readH);
    init(of(iso, imm, mut, mutH, readH),      iso, readH);
    init(of(iso, imm, mut, read, readH),      iso, readH);
    init(of(iso, imm, mutH, read, readH),     iso, readH);
    init(of(iso, mut, mutH, read, readH),     iso, readH);
    init(of(imm, mut, mutH, read, readH),     iso, readH);

    init(of(iso, imm, mut, mutH, read, readH), iso, readH);    
  }}