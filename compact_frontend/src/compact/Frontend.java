package compact;
import static compact.Frontend.K.*;
import static compact.Frontend.RC.*;
import static compact.Util.*;
import compact.Frontend.T.*;
import compact.Frontend.E.Call;
import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
public final class Frontend{
  @SuppressWarnings("serial")public static final class Fail extends RuntimeException{}
  static void no(boolean b){if(b)throw new Fail();}
  public static List<Literal>compile(String pk,Map<String,String>override,Map<String,String>files,List<Literal>lits){
    var other=lits.stream().collect(Collectors.toMap(Literal::name,d->d));var raw=new TreeMap<String,File>();
    files.forEach((path,content)->raw.put(path,new Parser(new Names(list(),list(),list(),null),tokens(content)).group(Parser::file)));
    var heads=filter(raw.keySet(),p->p.matches("(.*/)?_rank_[^/]*\\.[^/]*"));
    no(heads.size()!=1);var head=raw.get(heads.get(0));
    no(any(raw.values(),f->f!=head&&f.maps.size()+f.uses.size()>0));
    var ds=flat(raw.values(),f->f.decs.stream());var uses=map(head.uses,File.Use::out);
    var names=flat(ds,d->d.owner.decs.stream());no(dup(names));var strings=map(names,N::s);
    no(any(uses,strings::contains)||any(flat(ds,d->d.owner.gen.used.stream()),x->strings.contains(x)||uses.contains(x)));
    var map=new HashMap<>(override);for(var u:head.uses){var p=map.getOrDefault(u.in.pk(),u.in.pk());
      var in=p+"."+u.in.simple();map.put(u.out,in);no(p.equals(pk)||!any(other.keySet(),e->e.s.equals(in)));
    }var ctx=new Methods(new Pkg(pk,map,ds,new HashSet<>(names)),other);
    var res=ctx.headers();TS.check(res,other);return res;
  }
  public enum RC{
    imm,mut,read,iso,mutH,readH;
    boolean sub(RC other){return this==other||other==readH||this==iso||other==read&&!isH()||this==mut&&other==mutH;}
    boolean isH(){return this==mutH||this==readH;}boolean ro(){return this==read||this==imm;}
    boolean ii(){return this==iso||this==imm;}RC mutable(){return this==iso?mut:this;}
    RC ri(){return ii()?imm:read;}
  }
  public record N(String s,int arity){
    N qualify(String pk){return new N(pk+"."+s,arity);}
    N arity(int arity){return new N(s,arity);}
    String pk(){return s.replaceFirst("^(?![a-z]).*|\\..*","");}
    String simple(){return s.replaceFirst("^[a-z][^.]*\\.","");}
    boolean visible(){return!simple().startsWith("_");}
  }
  public record MN(String s,int arity){}
  public record B(String x,Set<RC>caps){
    static List<String>v(List<B>b){return b==null?list():map(b,B::x);}
    static B get(List<B>b,String name){return find(b,e->e.x.equals(name));}
  }
  enum K{
    Ws("\\s+|//[^\\n]*|/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"),
    Arrow("->"),LP("\\("),RP("\\)"),LB("\\{"),RBId("\\}[A-Za-z0-9_]+'*"),RB("\\}"),
    LA("(?<=[A-Za-z0-9_'"+K.op+"])(?<!\\*/)\\["),RA("\\]"),
    Hole("_"),Comma(","),Semi(";"),Implicit("::"),Colon(":"),Eq("="),Quote("'"),RIcap("read/imm"),Cap("readH|mutH|imm|iso|read|mut"),
    SF("[+-]"+K.flt),UF(K.flt),SI("[+-]"+K.nat),UI(K.nat),Str("\"[^\"\\n]*\""),Raw("`[^`\\n]*`"),
    Dot("\\._*[a-z]"+K.id),Up("(?:"+K.pk+"\\.)?_*[A-Z]"+K.id),
    Low("_*[a-z]"+K.id),Bad("'(?:(?!//|/\\*)[^'\\n\"`])*'(?![_a-z])"),Op("(?:(?!/\\*|\\*/|//)["+K.op+"])+"),
    End,Start,Curly,Square,Round;
    static final String pk="(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*",id="[A-Za-z0-9_]*'*",
      op="\\\\/#*\\-+%<>=!&^~?|",nat="[0-9](?:[0-9_]*[0-9])?",flt=nat+"\\."+nat+"(?:[eE][+-]?"+nat+")?(?:soft)?";
    final Pattern p;
    K(String regex){p=Pattern.compile(regex);}K(){this("");}
    int match(String s,int i){var m=p.matcher(s).useTransparentBounds(true).region(i,s.length());return m.lookingAt()?m.end()-i:-1;}
  }
  static boolean matches(String input,K...ks){return any(list(ks),k->k.match(input,0)==input.length());}
  static final K[]heads={Up,SF,UF,SI,UI,Raw,Str};
  record Token(K kind,String content,List<Token>tokens){boolean is(K...ks){return list(ks).contains(kind);}}
  static final String al="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  static final Map<K,Map<K,K>>groups=Map.of(Start,Map.of(End,End),LP,Map.of(RP,Round),LA,Map.of(RA,Square),LB,Map.of(RB,Curly,RBId,Curly));
  static List<Token>tokens(String s){s=s.replaceFirst("^\\uFEFF","").replaceAll("[\\r\\u2028\\u2029\\u0085]","\n");
    no(s.codePoints().anyMatch(c->al.indexOf(c)<0));var res=new Vector<Token>(list(new Token(Start,"",list())));for(int i=0;i<s.length();){
      K best=null;int len=0;for(var k:K.values()){var l=k.match(s,i);if(l>len){best=k;len=l;}}no(best==null);
      var t=new Token(best,s.substring(i,i+len),list());i+=len;if(t.is(Ws))continue;
      no(t.is(Bad)||t.is(LA)&&res.getLast().is(SI,UI,SF,UF));res.add(t);
    }
    res.add(new Token(End,"",list()));var it=res.iterator();return list(tree(it,it.next()));
  }
  static Token tree(Iterator<Token>it,Token open){
    var out=new Vector<Token>(list(open));while(true){var c=it.next();
      var g=groups.get(open.kind).get(c.kind);if(g!=null){out.add(c);return new Token(g,"",out);}
      if(groups.containsKey(c.kind)){out.add(tree(it,c));continue;}no(any(groups.values(),m->m.containsKey(c.kind)));out.add(c);
    }
  }
  sealed interface P{
    record X(String name)implements P{}
    record Lit(String self,List<PM>ms)implements P{}
    record Typed(RC r,C c,Lit l)implements P{}
    record Declared(RC r,Declaration dec)implements P{}
    record Args(RC r,List<T>types){}
    record Call(P e,String name,Args y,Pat pat,List<P>es)implements P{}
    record Implicit()implements P{}
  }
  record PS(RC r,String m,List<B>b,List<Par>ps,T t){}
  record PM(PS s,P body,boolean implicit){
    PM(PS s,P body){this(s,body,body!=null&&Frontend.implicit(body));}
    int arity(){return implicit?1:s.ps.size();}
  }
  static boolean implicit(P e){return switch(e){
    case P.Implicit _->true;case P.Call c->implicit(c.e)||any(c.es,Frontend::implicit);default->false;
  };}
  record Par(Pat xp,T t){}
  sealed interface Pat{
    Stream<String>names();
    record Name(String x)implements Pat{public Stream<String>names(){return Stream.of(x);}}
    record Des(List<List<String>>extract,String id)implements Pat{
      public Stream<String>names(){return extract.stream().map(e->e.getLast().substring(1)+id);}
    }
  }
  record Declaration(N name,List<B>b,List<C>cs,P.Lit l,Owner owner){}
  record File(Set<String>maps,List<Use>uses,List<Declaration>decs){record Use(N in,String out){}}
  record Names(List<String>v,List<String>Xs,List<String>hid,Owner owner){
    Names add(List<String>v,List<String>Xs){
      owner.vars.used.addAll(v);owner.gen.used.addAll(Xs);return new Names(push(this.v,v),push(this.Xs,Xs),hid,owner);
    }
  }
  record Key(RC r,MN name){}
  static final class Parser{
    Names names;final List<Token>tokens;int index=0;int limit;
    Parser(Names names,List<Token>tokens){this.names=names;this.tokens=tokens;limit=tokens.size();}
    Parser make(List<Token>tokens){return new Parser(names,tokens);}
    <A>A whole(Function<Parser,A>r){var res=r.apply(this);no(!end());return res;}
    boolean end(){return limit==index;}
    boolean see(int la,K...ks){return index+la<limit&&tokens.get(index+la).is(ks);}
    boolean see(K...ks){return see(0,ks);}
    Token take(K...ks){no(end());var t=tokens.get(index++);no(ks.length>0&&!t.is(ks));return t;}
    boolean fwd(boolean v){if(v)index+=1;return v;}
    <A>A group(Function<Parser,A>r){
      var p=make(tokens.get(index++).tokens);p.index=1;p.limit-=1;return p.whole(r);
    }
    Parser front(ToIntFunction<Parser>probe){
      var sub=make(tokens.subList(index,limit));int drop=probe.applyAsInt(sub);var res=make(tokens.subList(index,index+sub.index-drop));index+=sub.index;return res;
    }
    <A>List<A>by(ToIntFunction<Parser>probe,Function<Parser,A>elem){var res=new Vector<A>();while(!end())res.add(front(probe).whole(elem));return res;}
    <A>List<A>items(ToIntFunction<Parser>probe,Function<Parser,A>r){return group(p->p.by(probe,r));}
    <A>A prefix(ToIntFunction<Parser>probe,Function<Parser,A>first){var i=index;var p=front(probe);if(!end())return p.whole(first);index=i;return null;}
    int so(int mode,K k){while(!end()){if(!take().is(k))continue;if(mode==2)index-=1;return mode&1;}return 0;}
    P expr(){return posts(atom());}P posts(P e){while(!end())e=post(e);return e;}
    boolean isDec(){return see(heads)&&(see(1,Colon)||see(1,Square)&&see(2,Colon));}
    P atom(){
      if(see(Low)){var x=take().content;no(!names.v.contains(x));return new P.X(x);}
      if(see(Round))return group(Parser::expr);
      if(fwd(see(Implicit)))return new P.Implicit();if(see(Curly))return group(p->p.literal(false));
      var r=optCap();no(r!=null&&r.isH());if(isDec())return new P.Declared(r,declaration(false));
      return new P.Typed(or(r,imm),constructor(),see(Curly)?group(p->p.literal(false)):null);
    }
    RC cap(){return RC.valueOf(take(Cap).content);}RC optCap(){return see(Cap)?cap():null;}
    C constructor(){
      var c=name();List<T>types=see(Square)?items(comma,Parser::type):list();return new C(c.arity(types.size()),types);
    }
    N name(){var s=take(heads).content;
      no(names.Xs.contains(s)||names.hid.contains(s));var res=new N(s,0);no(!res.pk().isEmpty()&&!res.visible());return res;
    }
    T type(){
      if(fwd(see(RIcap)))return new RI(variable(false));var r=optCap();
      if(see(heads)&&!names.Xs.contains(tokens.get(index).content))return new R(or(r,imm),constructor());
      var res=variable(false);return r==null?res:new RX(r,res);
    }
    X variable(boolean mustNew){
      var c=take(Up,"[^.]*");no(mustNew?names.Xs.contains(c)||names.hid.contains(c):!names.Xs.contains(c));return new X(c);
    }
    P post(P receiver){
      if(see(SF,SI)){var num=take().content;
        return new P.Call(receiver,num.substring(0,1),null,null,list(new P.Typed(imm,new C(new N(num.substring(1),0),list()),null)));
      }
      var m=take(Dot,Op).content;var sq=see(Square)?group(Parser::arguments):null;
      if(see(Round))return new P.Call(receiver,m,sq,null,items(Parser::exprEnd,Parser::expr));
      var xpat=see(Low,Curly)&&see(1,Eq)?pattern():null;fwd(xpat!=null);
      if(end()||see(Dot,Op,Colon)){no(xpat!=null);return new P.Call(receiver,m,sq,null,list());}
      var atom=atom();var v=xsOf(xpat).toList();fresh(v);
      no(xpat instanceof Pat.Des&&v.size()>31);names=names.add(v,list());
      return new P.Call(receiver,m,sq,xpat,xpat==null?list(atom):list(atom,posts(post(new P.X("")))));
    }
    Pat pattern(){return see(Low)?new Pat.Name(binder()):group(Parser::destruct);}
    Pat.Des destruct(){
      var id=tokens.get(limit).content.substring(1);
      var chains=by(comma,p->p.by(q->{q.take();return 0;},q->q.take(Dot).content));
      no(chains.size()==0||any(chains,List::isEmpty));var res=new Pat.Des(chains,id);
      no(res.names().anyMatch(x->!matches(x,Low)||matches(x,Cap)));return res;
    }
    P.Args arguments(){
      var hasCap=see(Cap)&&tokens.get(index+1).is(Comma,RA);var r=hasCap?cap():null;
      if(hasCap&&!end())take(Comma);return new P.Args(r,by(comma,Parser::type));
    }
    String binder(){var x=take(Low,Hole).content;no(names.v.contains(x));return x;}
    P.Lit literal(boolean top){
      no(tokens.get(limit).is(RBId));var self=fwd(see(Quote))?binder():top?"this":"_";
      no(top&&!self.equals("this"));if(!self.equals("_"))names=names.add(list(self),list());
      var ms=by(p->p.so(1,Semi),p->p.method(top));
      var ns=map(filter(ms,m->m.s.m!=null),m->new Key(m.s.r,new MN(m.s.m,m.arity())));no(dup(ns));
      no(any(ns,nn->nn.r==null&&any(ns,o->o.name.equals(nn.name)&&o.r!=null)));
      no(dup(map(filter(ms,m->m.s.m==null),PM::arity)));return new P.Lit(self,ms);
    }
    Stream<String>xsOf(Pat xp){return Stream.ofNullable(xp).flatMap(Pat::names);}
    void fresh(List<String>v){no(dup(v)||any(v,names.v::contains));}
    PM method(boolean top){
      var s=prefix(p->p.so(1,Arrow),Parser::signature);if(s!=null){var v=flat(s.ps,p->xsOf(p.xp));fresh(v);
        names=names.add(v,B.v(s.b));var m=new PM(s,whole(Parser::expr));
        no(m.implicit&&s.ps.size()>0||any(s.ps,p->p.xp instanceof Pat.Des)&&v.size()>32);return m;
      }
      if(!(see(Dot,Op)||see(Cap)&&see(1,Dot,Op)))return new PM(bare,whole(Parser::expr));no(!top);return new PM(signature(),null);
    }
    PS signature(){
      var r=optCap();no(r!=null&&(r.isH()||r==iso));
      var m=see(Dot,Op)?take().content:null;var b=see(Square)?bounds(true):null;
      names=names.add(list(),B.v(b));
      var ps=see(Round)?items(comma,Parser::parameter):see(Colon)?List.<Par>of():by(comma,Parser::parameter);
      var t=fwd(see(Colon))?type():u;no(!end());var v=flat(ps,p->xsOf(p.xp));
      no(dup(v));names.owner.vars.used.addAll(v);return new PS(r,m,b,ps,t);
    }
    Par parameter(){
      var named=see(Low,Hole,Curly);var x=named&&!fwd(see(Hole))?pattern():null;
      var p=new Par(x,named?fwd(see(Colon))?type():u:type());no(!end());return p;
    }
    List<B>bounds(boolean mustNew){var res=items(Parser::boundEnd,p->p.bound(mustNew));no(dup(B.v(res)));return res;}
    B bound(boolean mustNew){
      var x=variable(mustNew).name;if(end())return new B(x,caps(imm));take(Colon);no(end());if(!see(Op)){
        var caps=by(comma,Parser::cap);no(dup(caps));return new B(x,EnumSet.copyOf(caps));
      }
      return switch(take(Op).content){case "**"->new B(x,allRC);case "*"->new B(x,caps(imm,mut,read));default->throw new Fail();};
    }
    Declaration declaration(boolean top){
      var c=name();no(c.s.contains(".")||primitive(c.s));
      var b=see(Square)?bounds(top):List.<B>of();var outer=names;var owner=top?new Owner():names.owner;
      names=new Names(names.v,list(),push(names.hid,names.Xs),owner).add(list(),B.v(b));owner.decs.add(c=c.arity(b.size()));take(Colon);
      var cs=required(prefix(p->p.so(2,Curly),p->p.by(comma,Parser::constructor)));no(dup(cs));
      var l=group(p->p.literal(top));names=outer;return new Declaration(c,b,cs,l,owner);
    }
    File file(){
      var maps=new HashSet<String>();var uses=new Vector<File.Use>();front(Parser::headEnd).whole(p->{
        if(!p.see(Low))return null;no(!p.tokens.get(--p.limit).is(Semi));return p.by(q->q.so(1,Semi),q->q.directive(maps,uses));
      });
      return new File(maps,uses,by(p->p.so(0,Curly),p->p.declaration(true)));
    }
    String take(K kind,String regex){var s=take(kind).content;no(!s.matches(regex));return s;}
    Object directive(HashSet<String>maps,Vector<File.Use>uses){
      if(take(Low,"map|use").equals("map")){
        var in=take(Low,K.pk);take(Low,"as");take(Low,K.pk);
        take(Low,"in");no(!maps.add(in+" "+take(Low,K.pk)));
      }else{
        var a=name();take(Low,"as");
        var z=take(Up,"[^.]*");no(any(uses,u->u.in.equals(a)||u.out.equals(z)));
        uses.add(new File.Use(a,z));
      }no(!end());return null;
    }
    int exprEnd(){var inColon=false;while(!end()){
      var t=take();if(t.is(Comma)&&!inColon)return 1;inColon=t.is(Colon)||inColon&&t.is(Square,Comma,Up);
    }return 0;}
    int boundEnd(){while(!end()){if(take().is(Comma)&&!see(Cap))return 1;}return 0;}
    int headEnd(){while(!(end()||isDec()))take();return 0;}
    static final ToIntFunction<Parser>comma=p->p.so(1,Comma);
  }
  record Pkg(String name,Map<String,String>map,List<Declaration>decs,Set<N>names){}
  record Scope(HashSet<String>used,HashMap<String,Integer>seq){Scope(){this(new HashSet<>(),new HashMap<>());}}
  record Owner(Scope gen,Scope vars,Vector<N>decs){Owner(){this(new Scope(),new Scope(),new Vector<>());}}
  record Fresh(Scope top,HashSet<String>reserved,HashMap<N,Owner>owners,String pk){
    Fresh(Pkg p){this(new Scope(),new HashSet<>(),new HashMap<>(),p.name);
      top.used.addAll(map(p.names,N::simple));top.used.addAll(p.map.keySet());
      for(var d:p.decs){reserved.addAll(d.owner.gen.used);owners.put(d.name.qualify(pk),d.owner);}
    }
    N type(N hint,int arity){
      var res=new N(pk+"."+fresh(hint.simple(),top,list(reserved)),arity);owners.put(res,owners.get(hint));return res;
    }
    E copy(E e){return switch(e){
      case Call c->c.children(copy(c.e),map(c.es,this::copy));
      case Literal l->{no(!l.anon);var name1=type(l.name,l.name.arity);
        yield new Literal(l.r,name1,l.b,l.cs,l.self,map(l.ms,m->new M(m.o(l.name,name1).s,m.v,copy(m.e))),l.t,true,l.expanded);
      }
      case null,default->e;
    };}
    static String fresh(String hint,Scope s,List<Collection<String>>checks){
      var base=hint.replaceAll("[^A-Za-z0-9]","").replaceFirst("(?<=.{4}).*","");var abc="abcdefghjkmnpqrstuvwxyz";if(base.matches("[A-Z].*"))abc=abc.toUpperCase();for(int n=s.seq.getOrDefault(base,1);;n+=1){
        var sb=new StringBuilder();for(int k=n;k>0;k=(k-1)/23)sb.append(abc.charAt((k-1)%23));
        var cand="_"+sb.reverse()+base;if(s.used.contains(cand)||any(checks,e->e.contains(cand)))continue;
        s.used.add(cand);s.seq.put(base,n+1);return cand;
      }
    }
  }
  static final N str=base("Str",0),nat=base("Nat",0),integer=base("Int",0),floating=base("Float",0),
    widen=base("WidenTo",1),sealed=base("Sealed",0),cf=base("CaptureFree",0),identity=base("BaseId",2),log=base("FileLog",0),
    container=base("BaseContainer",1),voidName=base("Void",0),main=base("Main",0),fin=base("Final",1);
  static final List<N>concrete=List.of(base("SystemAttenuator",0),base("InfoMain",0),base("DataRead",0),log,base("InMemoryLog",1));
  static final List<N>claims=List.of(base("OpenWith",1),base("OpenWith",2),base("Shortcut",1),base("Shortcut",2),base("PreLoadIcon",1));
  static Set<RC>caps(RC first,RC...rest){return EnumSet.of(first,rest);}
  static final Set<RC>ii=caps(iso,imm),plain=caps(iso,imm,mut,read),allRC=EnumSet.allOf(RC.class);
  static N base(String s,int n){return new N("base."+s,n);}static boolean has(List<C>cs,N magic){return any(cs,c->c.name.equals(magic));}
  static boolean primitive(String name){return"+-1234567890\"`".contains(name.substring(0,1));}
  static String quoted(T t){var s=t instanceof R(_,var e)?e.name.simple():"";no(!s.matches("[\"`].*"));return s.substring(1,s.length()-1);}
  static Literal from(N n,Function<N,Literal>map,Map<N,Literal>other){
    var res=or(map.apply(n),other.get(n));
    if(res!=null||!n.pk().equals("base")||!primitive(n.simple()))return res;var s=n.simple();
    var lit=matches(s,Str,Raw)?str:matches(s,UI)?nat:matches(s,SI)?integer:floating;
    var sup=from(lit,map,other);var ms=map(sup.ms,m->m.signature(new S(m.s.r,m.s.m,m.s.b,m.s.types,m.s.t,n,false,m.s.idx)));
    return new Literal(imm,n,list(),push(new C(lit,list()),sup.cs),"this",ms,u,true,false);
  }
  static int bits(String s){return new BigInteger(s.replace("_","")).bitLength();}
  static boolean floatOk(String raw){
    var soft=raw.endsWith("soft");var ns=raw.replace("soft","").replace("_","");var d=Double.parseDouble(ns);
    return Double.isFinite(d)&&(soft||(d==0?new BigDecimal(ns.replaceAll("[eE].*","")):new BigDecimal(ns).subtract(new BigDecimal(d))).signum()==0);
  }
  static final T u=U.Instance;static final PS bare=new PS(null,null,null,list(),u);
  public sealed interface T{
    default boolean tv(){return!und();}
    default RC erc(){return null;}default int depth(){return 1;}
    record X(String name)implements T{}
    record RX(RC r,X x)implements T{public RC erc(){return r;}}
    record RI(X x)implements T{}
    record C(N name,List<T>types){}
    record R(RC r,C c)implements T{
      R withTs(List<T>types){return with(r,types);}
      R with(RC r,List<T>types){return new R(r,new C(c.name,types));}
      public boolean tv(){return all(c.types,T::tv);}public int depth(){return 1+c.types.stream().mapToInt(T::depth).max().orElse(1);}
      public RC erc(){return r;}
    }
    enum U implements T{Instance}
    record Amb(List<T>cs)implements T{}
    default boolean und(){return this==u||this instanceof Amb;}
    default T rc(RC r){return und()?this:this instanceof R w?new R(r,w.c):new RX(r,new X(variable(this)));}
    default Stream<String>ftv(){return this instanceof R w?typeFree(w.c.types):Stream.ofNullable(variable(this));}
    default T ri(){return switch(this){
      case X x->new RI(x);case R(var r,var c)->new R(r==null?null:r.ri(),c);case RX(var r,var x)->new RX(r.ri(),x);default->this;
    };}
  }
  public sealed interface E{
    T t();E t(T t);
    default Stream<E>children(){return switch(this){
      case Literal l->l.ms.stream().flatMap(m->Stream.ofNullable(m.e));case Call c->cat(Stream.of(c.e),c.es.stream());default->Stream.of();
    };}
    record X(String name,T t)implements E{
      public E t(T t){return new X(name,t);}
    }
    record Call(E e,MN name,RC r,List<T>y,List<E>es,T t,boolean written)implements E{
      Call children(E e,List<E>es){return new Call(e,name,r,y,es,t,written);}
      public Call t(T t){return new Call(e,name,r,y,es,t,written);}
    }
  }
  public record Literal(RC r,N name,List<B>b,List<C>cs,String self,List<M>ms,T t,boolean anon,boolean expanded)implements E{
    public Literal t(T t){return new Literal(r,name,b,cs,self,ms,t,anon,expanded);}
    Literal header(List<C>cs,List<M>ms,boolean ex){return new Literal(r,name,b,cs,self,ms,t,anon,ex);}
    R self(RC r){return new R(r,new C(name,vars(b)));}
  }
  public record M(S s,List<String>v,E e){
    M(S s){this(s,Collections.nCopies(s.types.size(),"_"),null);}
    M signature(S s){return new M(s,v,e);}
    M o(N a,N b){return Objects.equals(s.o,a)?signature(s.o(b)):this;}
  }
  public record S(RC r,MN m,List<B>b,List<T>types,T t,N o,boolean abs,int idx){
    S types(List<T>types,T t){return new S(r,m,b,types,t,o,abs,idx);}
    S o(N o){return new S(r,m,b,types,t,o,abs,idx);}
    S subst(List<B>b,List<String>v,List<T>types){return new S(r,m,b,rename(this.types,v,types),rename(t,v,types),o,abs,idx);}
  }
  static<A>A or(A a,A b){return a==null?b:a;}
  static<A>A required(A a){no(a==null);return a;}
  static final class IG{
    record Frame(RC r,List<B>b,HashMap<String,T>vars){}
    final Vector<Frame>fs=new Vector<>(list(new Frame(null,list(),new HashMap<>())));
    int at(String x){return fs.indexOf(find(fs,f->f.vars.containsKey(x)));}
    T get(String x){return find(map(fs,f->f.vars.get(x)),Objects::nonNull);}
    T adapted(String x){var t=get(x);var fxs=t.ftv().toList();
      for(var f:fs.subList(at(x)+1,fs.size())){no(!B.v(f.b).containsAll(fxs));t=adapt(t,f.r,f.b);}return t;
    }
    static T adapt(T t,RC r,List<B>b){if(t.und())return t;var caps=TS.kinds(b,t);
      if(r==imm||ii.containsAll(caps))return t.rc(imm);if(r==read){
        if(t.erc()==mut||t.erc()==read)return t.rc(read);
        if(t instanceof X||t instanceof RI)return t.ri();
      }return caps(imm,mut,read).containsAll(caps)?t:t.ri();
    }
    Object declare(String x,T t){return fs.getLast().vars.put(x,t);}
    void declare(M m){zip(m.v,m.s.types,this::declare);}
    Object snap(){return map(fs,f->new Frame(f.r,f.b,new HashMap<>(f.vars)));}
  }
  static C normC(C c){return((R)norm(new R(null,c))).c;}
  static T norm(T t){no(!t.tv());return fill(t);}
  static int size(T t){return t instanceof R w?1+size(w.c.types.stream()):1;}
  static int size(Stream<T>s){return s.mapToInt(Frontend::size).sum();}
  static int size(E e){return size(e.t())+e.children().mapToInt(Frontend::size).sum()+switch(e){
    case Call c->size(c.y.stream());
    case Literal l->size(ts(l));default->0;
  };}
  static Stream<T>ts(Literal l){return cat(l.cs.stream().map(c->new R(null,c)),l.ms.stream().flatMap(m->push(m.s.types,m.s.t).stream()));}
  static T fill(T t){return t instanceof R(var r,var c)?new R(or(r,imm),new C(c.name,map(c.types,Frontend::fill))):t;}
  static T rename(T t,List<String>v,List<T>types){
    if(t instanceof R w)return w.withTs(rename(w.c.types,v,types));
    var x=variable(t);if(x==null)return t;
    T a=v.contains(x)?types.get(v.indexOf(x)):new X(x);
    return t instanceof RI?a.ri():t instanceof RX?a.rc(t.erc()):a;
  }
  static List<T>rename(List<T>tsi,List<String>v,List<T>types){return map(tsi,ti->rename(ti,v,types));}
  static String variable(T t){return switch(t){
    case X x->x.name;case RX(_,var x)->x.name;case RI(var x)->x.name;default->null;
  };}
  static Stream<String>typeFree(List<T>ts){return ts.stream().flatMap(T::ftv);}
  static List<T>vars(List<B>b){return map(b,e->new X(e.x));}
  static List<T>qs(int n){return Collections.nCopies(n,u);}
  record MS(RC r,List<String>v,List<B>cb,List<T>cas,List<B>mb,List<T>ps,T ret){
    MS arguments(List<T>cas){return new MS(r,v,cb,cas,mb,ps,ret);}
    T inst(T t,List<T>y){return rename(t,v,push(cas,fixTargs(y,mb.size())));}
    static List<T>fixTargs(List<T>y,int n){return y.size()>n?y.subList(0,n):push(y,qs(n-y.size()));}
  }
  static Stream<String>free(IG g,E e){return switch(e){
    case E.X(var name,var t)->cat(t.ftv(),Stream.ofNullable(g.get(name)).flatMap(T::ftv));
    case Literal l->cat(l.b.stream().map(B::x),supFree(l.cs),methodFree(g,l.ms));
    case Call(var ei,_,_,var y,var es,_,_)->cat(free(g,ei),typeFree(y),es.stream().flatMap(x->free(g,x)));
  };}
  static Stream<String>supFree(List<C>cs){return cs.stream().flatMap(c->typeFree(c.types));}
  static Stream<String>methodFree(IG g,List<M>ms){return ms.stream().flatMap(m->cat(typeFree(m.s.types),m.s.t.ftv(),Stream.ofNullable(m.e).flatMap(ei->free(g,ei))).filter(x->!B.v(m.s.b).contains(x)));}
  record XE(String x,P e){}
  static final class Methods{
    final Pkg p;final Map<N,Literal>other;final Fresh fresh;final HashMap<N,Literal>cache=new HashMap<>();
    final HashMap<E,Object>memo=new HashMap<>();int deep,cap;N owner;final Vector<String>implicits=new Vector<>();final Vector<Literal>decs=new Vector<>();
    Methods(Pkg p,Map<N,Literal>other){this.p=p;this.other=other;fresh=new Fresh(p);}
    String fresh(String hint){return Fresh.fresh(hint,fresh.owners.get(owner).vars,list());}
    N f(N tn){
      var pN=tn.pk();if(pN.isEmpty()&&primitive(tn.s))return tn.qualify("base");
      var full=new N(pN.isEmpty()?p.map.getOrDefault(tn.s,p.name+"."+tn.s):p.map.getOrDefault(pN,pN)+"."+tn.simple(),tn.arity);
      no(!(full.pk().equals(p.name)?p.names.contains(new N(full.simple(),full.arity)):other.containsKey(full)));return full;
    }
    T type(T t){return t instanceof R(var r,var c)?new R(r,constructor(c)):t;}
    E expr(P e){return switch(e){
      case P.X x->new E.X(x.name,u);case P.Implicit _->new E.X(implicits.getLast(),u);
      case P.Typed t->literal(t.r,list(constructor(t.c)),or(t.l,new P.Lit("_",list())));
      case P.Declared c->{var name=f(c.dec.name);fresh.owners.put(name,fresh.owners.get(owner));
        yield used(declaration(name,or(c.r,imm),c.dec),c.dec.l.self);
      }
      case P.Lit l->literal(null,list(),l);
      case P.Call c0->{
        var c=c0.pat!=null?desugar(c0):c0;var sq=or(c.y,new P.Args(null,list()));
        yield new Call(expr(c.e),new MN(c.name,c.es.size()),sq.r,map(sq.types,this::type),map(c.es,this::expr),u,c.y!=null);
      }
    };}
    C constructor(C c){var s=c.name.s;
      no(primitive(s)&&(matches(s,UI)&&bits(s)>64||matches(s,SI)&&bits(s)>63||matches(s,SF,UF)&&!floatOk(s)));
      return new C(f(c.name),map(c.types,this::type));
    }
    String parameter(Par p,boolean patterns){return switch(p.xp){
      case null->name("_");case Pat.Name(var x)->patterns?fresh(x):x;
      case Pat.Des _->fresh("div");
    };}
    List<M>methods(List<PM>ms){return seq(ms.size(),i->method(ms.get(i),i));}
    M method(PM m,int idx){var q=m.s;var original=q.ps;var types=map(original,p->type(p.t));if(m.implicit)types=push(types,u);
      var s=new S(q.r,q.m==null?null:new MN(q.m,m.arity()),q.b,types,type(q.t),null,m.body==null,idx);
      if(m.body==null)return new M(s);var body=m.body;
      var patterns=any(original,p->p.xp instanceof Pat.Des);
      var ps=map(original,p->parameter(p,patterns));
      var xpats=flat(zip(ps,original,(x,p)->xpat(p.xp,x)),y->y);if(m.implicit){
        var p=fresh("impl");ps=push(ps,p);implicits.add(p);
      }if(patterns){
        var fl=lambda(map(xpats,xe->new Par(new Pat.Name(xe.x),u)),body);
        body=new P.Call(new P.Typed(imm,new C(base("Destruct",0),list()),null),"#",null,null,push(map(xpats,XE::e),fl));
      }
      var e=expr(body);if(m.implicit)implicits.removeLast();return new M(s,ps,e);
    }
    Stream<XE>xpat(Pat xp,String lowered){return switch(xp){
      case null->Stream.of();
      case Pat.Des d->zip(d.extract,d.names().toList(),(e,x)->{
        P res=new P.X(lowered);for(var m:e)res=new P.Call(res,m,null,null,list());return new XE(x,res);
      }).stream();
      case Pat.Name(var x)->x.equals(lowered)?Stream.of():Stream.of(new XE(x,new P.X(lowered)));
    };}
    Literal literal(RC r,List<C>impl,P.Lit l){var ms=methods(l.ms);
      return used(new Literal(r,fresh.type(owner,0),list(),impl,name(l.self),ms,u,true,false),l.self);
    }
    String name(String x){return x.equals("_")?fresh("0"):x;}
    static Literal used(Literal l,String x){no(!x.equals("_")&&TS.count(x,l,false)==0);return l;}
    Literal declaration(N name,RC r,Declaration d){var cs=map(d.cs,this::constructor);
      no(Core.distinct(d.b,cs).size()<cs.size());
      var l=new Literal(r,name,d.b,cs,name(d.l.self),methods(d.l.ms),u,false,false);decs.add(l);return l;
    }
    P.Call desugar(P.Call c){
      var x=fresh("eqS");
      return new P.Call(c.e,c.name,c.y,null,list(c.es.get(0),lambda(list(new Par(c.pat,u),new Par(new Pat.Name(x),u)),receiver(c.es.get(1),new P.X(x)))));
    }
    static P lambda(List<Par>ps,P body){return new P.Lit("_",list(new PM(new PS(null,null,null,ps,u),body,false)));}
    P receiver(P par,P atom){
      return par instanceof P.Call c?new P.Call(receiver(c.e,atom),c.name,c.y,c.pat,c.es):atom;
    }
    List<Literal>headers(){for(var di:p.decs){owner=f(di.name);declaration(owner,mut,di);}var rem=new LinkedHashMap<N,Literal>();
      decs.forEach(d->rem.put(d.name,d));var acc=new Vector<Literal>();while(rem.size()>0){
        var layer=filter(rem.values(),d->!any(d.cs,c->rem.containsKey(c.name)));
        no(layer.size()==0);for(var d:layer){
          rem.remove(d.name);register(expand(d,false));if(d.self.equals("this"))acc.add(cache.get(d.name));
        }
      }deep=cat(cache.values().stream(),other.values().stream()).flatMap(Frontend::ts).mapToInt(T::depth).max().orElse(1);
      return map(acc,di->di.header(di.cs,map(di.ms,m->body(di,m)),false));
    }
    List<C>parents(C c){var d=from(c.name);return d==null?list():d.cs.stream().map(ci->new C(ci.name,rename(ci.types,B.v(d.b),c.types))).distinct().toList();
    }
    S alpha(M m,C c,Literal child,List<String>scope){var s=m.s;var xs=new Vector<>(B.v(from(c.name).b));
      var ts=new Vector<>(c.types);var bs=new Vector<B>();var gen=fresh.owners.get(child.name).gen;var top=fresh.top.used;for(var b:s.b){var x=b.x;
        if(!gen.used.contains(x)&&!top.contains(x)&&!scope.contains(x)){bs.add(b);continue;}xs.add(x);
        var next=Fresh.fresh(x,gen,list(top,push(B.v(s.b),scope)));fresh.reserved.add(next);ts.add(new X(next));bs.add(new B(next,b.caps));
      }return s.subst(bs,xs,ts);
    }
    Literal from(N name){return Frontend.from(name,cache::get,other);}
    Literal expand(Literal d,boolean expanded){
      var implied=flat(d.cs,c->parents(c).stream());
      var supers=Core.distinct(d.b,push(d.cs,implied.stream().sorted(Comparator.comparing(Print::of)).toList()));
      var signatures=flat(filter(d.cs,c->!implied.contains(c)),c->from(c.name).ms.stream().map(m->alpha(m,c,d,list())));
      var res=d.header(supers,pair(d.ms,signatures,d),expanded);
      magic(res,supers);return res;
    }
    Literal implement(Literal d,C c,List<B>scope){var dd=from(c.name);
      return d.header(push(c,parents(c)),pair(d.ms,dd==null?list():map(dd.ms,m->alpha(m,c,d,B.v(scope))),d),true);
    }
    void magic(Literal d,List<C>supers){no(filter(supers,c->c.name.equals(widen)).size()>1);
      if(has(supers,identity)){no(d.ms.size()!=1);var m=d.ms.get(0);var s=m.s;
        no(!s.m.equals(new MN("#",1))||m.e==null&&!s.abs&&!has(from(s.o).cs,identity));
      }
      if(has(supers,log)){var s=d.name.simple();no(s.matches(".*('|_[a-z]).*"));var f=s.replaceAll("[A-Z]","_$0").toLowerCase(Locale.ROOT).substring(1);
        no(f.matches("con|prn|aux|nul|(com|lpt)[1-9]|_rank_.*")||f.length()+d.name.pk().length()>184);
      }
      var cl=filter(supers,c->claims.contains(c.name));no(cl.size()>0&&!has(supers,main));var exts=new HashSet<String>();
      for(var c:cl){no(!(c.types.get(0)instanceof R(_,var i)&&i.types.size()==0));if(c.types.size()==1)continue;
        var ext=quoted(c.types.get(1));
        no(!ext.matches("[a-z0-9]{1,16}")||ext.equals("fearless")||c.name.simple().equals("Shortcut")!=ext.matches("fapp[0-9]{3}")||!exts.add(ext));
      }
      for(var c:filter(supers,x->x.name.equals(fin))){var m=quoted(c.types.get(0));no(!matches(m,Dot,Op));
        no(any(supers,o->!o.name.equals(fin)&&any(parents(o),p->p.name.equals(fin)&&quoted(p.types.get(0)).equals(m)))&&any(d.ms,mi->mi.s.m.s().equals(m)&&d.name.equals(mi.s.o)));
      }
      no(d.b.size()>0&&(has(supers,main)||any(concrete,n->has(supers,n))&&all(d.ms,m->m.e!=null||!m.s.abs)));
      no(has(supers,sealed)&&any(supers,c->!c.name.pk().equals(d.name.pk())&&has(from(c.name).cs,sealed)));
    }
    void register(Literal d){
      cache.put(d.name,new Literal(or(d.r,imm),d.name,d.b,map(d.cs,Frontend::normC),d.self,map(d.ms,m->m.signature(Core.merge(m.s,m.s))),u,d.anon,false));
    }
    M name(M m,Vector<S>ss){
      var arity=m.s.types.size();for(var abs:list(true,false)){
        var match=filter(ss,s->s.m.arity==arity&&(s.abs||!abs));ss.removeAll(match);
        var count=match.stream().map(s->s.m).distinct().count();no(count>1);if(count==1){var s=m.s;
          return m.signature(new S(s.r,match.get(0).m,s.b,s.types,s.t,s.o,s.abs,s.idx));
        }
      }throw new Fail();
    }
    List<M>pair(List<M>ms,List<S>sigs,Literal o){var res=new Vector<M>();var ss=new Vector<>(sigs);var ns=new Vector<>(filter(sigs,s->!any(ms,m->Objects.equals(m.s.m,s.m))));
      for(var m:Util.<M>push(filter(ms,x->x.s.m!=null),map(filter(ms,x->x.s.m==null),x->name(x,ns)))){
      var name=m.s.m;var r=m.s.r;
      var taken=filter(ss,s->s.m.equals(name)&&(r==null||r==s.r));ss.removeAll(taken);
      var match=group(taken,s->s.r);
      if(r==null&&match.size()>1&&noH(or(o.r,or(o.t.erc(),imm))).ro()){
        var dead=match.remove(mut);if(dead!=null)ss.addAll(dead);
      }var first=true;
      for(var matches:match.size()==0?list(List.<S>of()):match.values()){
        var mi=first?m:new M(m.s,m.v,fresh.copy(m.e));first=false;res.add(pair(matches,mi,o));
      }
    }
      group(ss,s->new Key(s.r,s.m)).values().forEach(v->res.add(pair(v,null,o)));return res;
    }
    M pair(List<S>ss,M om,Literal o){
      if(om==null&&ss.size()==1)return new M(ss.get(0));
      var s=om==null?new S(null,null,null,qs(ss.get(0).m.arity),u,null,false,0):om.s;
      if(ss.size()==0){no(any(s.types,t->t==u)||s.t==u);
        return om.signature(new S(or(s.r,imm),s.m,or(s.b,list()),s.types,s.t,o.name,om.e==null,s.idx));
      }
      var b=or(s.b,ss.get(0).b);no(any(ss,e->!map(e.b,B::caps).equals(map(b,B::caps))));
      var aligned=map(ss,e->e.subst(b,B.v(e.b),vars(b)));var first=aligned.get(0);
      var types=seq(s.types.size(),i->s.types.get(i)==u?agreement(o,aligned,e->e.types.get(i)):s.types.get(i));
      var res=s.t==u?agreement(o,aligned,S::t):s.t;
      var impl=om!=null?List.<N>of():aligned.stream().filter(e->!e.abs&&o.cs.stream().flatMap(c->cat(Stream.of(c),from(c.name).cs.stream())).map(c->from(c.name)).noneMatch(d->!d.name.equals(e.o)&&has(d.cs,e.o)&&any(d.ms,m->m.s.o.equals(d.name)&&m.s.m.equals(e.m)&&m.s.r==e.r))).map(e->e.o).distinct().toList();no(impl.size()>1);
      var out=new S(or(s.r,first.r),first.m,b,types,res,impl.size()==1?impl.get(0):o.name,om==null?impl.size()==0:om.e==null,s.idx);
      return om==null?new M(out):om.signature(out);
    }
    T agreement(Literal lit,List<S>ss,Function<S,T>f){var res=map(ss,f);
      var b=push(lit.b,ss.get(0).b);var first=fill(res.get(0));
      no(!all(res,t->TS.equivalent(b,first,fill(t))));return res.get(0);
    }
    M body(Literal di,M m){
      if(m.e==null)return m;var ei=meet(m.e,m.s.t);cap=deep*size(ei);var g=new IG();g.declare(m);
      g.declare(di.self,di.self(has(di.cs,cf)?imm:m.s.r));var b=push(di.b,m.s.b);
      return new M(m.s,m.v,new Core(b,this).core(solve(b,g,ei),m.e));
    }
    E meet(E e,T t){
      if(e instanceof Literal l&&l.t.tv())return e;e=ascribe(e,t,null);
      return e.t(meet(e.t(),t));
    }
    T below(R sub,R sup){
      var d=from(sub.c.name);if(d==null)return null;var ps=filter(d.cs,c->c.name.equals(sup.c.name));if(ps.size()==0)return null;
      var res=sub.with(meet(sub.r,sup.r),meet(sub.c.types,meet(map(ps,c->refine(B.v(d.b),new R(null,c),sup)))));return res.tv()||!sup.tv()?res:sup;
    }
    T meet(T a,T z){
      if(z.und())return a==u?z:a;if(a.und()||a.equals(z))return z;
      if(a instanceof RI(var p)&&p.equals(z))return a;if(z instanceof RI(var q)&&q.equals(a))return z;
      if(a instanceof R p&&z instanceof R q)return p.c.name.equals(q.c.name)?p.with(meet(p.r,q.r),meet(p.c.types,q.c.types)):or(below(p,q),or(below(q,p),p));
      if(!(a instanceof RX p&&z instanceof RX(var rc2,var q))||!p.x.equals(q))return a;
      return p.rc(meet(p.r,rc2));
    }
    static RC meet(RC a,RC b){
      if(a==null||b==null)return or(a,b);var x=noH(a);var y=noH(b);
      return x==y||y==iso||y==read&&x!=iso?x:x==iso||x==read?y:imm;
    }
    static RC noH(RC a){return a==readH?read:a==mutH?mut:a;}
    T join(T a,T z){
      if(z==u)return a;if(a==u||a.equals(z))return z;
      var cands=push(candidates(a),candidates(z));for(var top:cands){var res=above(top,cands);if(res!=null)return res;}
      if(!all(cands,c->c instanceof R))return new Amb(cands);
      var heads=cands.stream().map(c->new Vector<>(map(parents(((R)c).c),C::name))).reduce((p,q)->{p.retainAll(q);return p;}).get();
      var minimal=filter(heads,h->!any(heads,h2->!h2.equals(h)&&from(h2)!=null&&has(from(h2).cs,h)));
      return minimal.size()==1?above(sup((R)cands.get(0),minimal.get(0)),cands):new Amb(cands);
    }
    static List<T>candidates(T t){return t instanceof Amb(var cs)?cs:list(t);}
    T above(T top,List<T>cands){
      T res=top;for(var c:cands){var up=c instanceof R r&&top instanceof R rt?r.c.name.equals(rt.c.name)?c:sup(r,rt.c.name):variable(c)!=null&&variable(c).equals(variable(top))?c:null;if(up==null)return null;
        res=res instanceof R p&&up instanceof R q?p.with(join(p.r,q.r),meet(p.c.types,q.c.types)):res instanceof RX p&&up instanceof RX q?p.rc(join(p.r,q.r)):meet(res,up);}return res;
    }
    static RC join(RC a,RC b){
      if(a==null||b==null)return or(a,b);var x=noH(a);var y=noH(b);return x==y||y==iso?x:x==iso?y:read;
    }
    List<T>meet(List<T>a,List<T>z){return zip(a,z,this::meet);}
    List<T>meet(List<List<T>>tss){return tss.stream().reduce(this::meet).get();}
    E solve(List<B>b,IG g,E e){
      if(list(g.snap(),cache.size()).equals(memo.get(e)))return e;var grew=0;while(true){var s=g.snap();var oe=next(b,g,e);
        if(oe.equals(e)&&s.equals(g.snap())){memo.put(e,list(s,cache.size()));return e;}
        grew=oe.t().depth()>e.t().depth()?grew+1:0;no(grew==50||oe.t().depth()>cap);e=oe;
      }
    }
    List<E>solve(List<B>b,IG g,List<E>es){return map(es,ei->solve(b,g,ei));}
    List<E>expect(List<E>es,MS m,List<T>y){return zip(es,m.ps,(e,p)->meet(e,m.inst(p,y)));}
    E next(List<B>b,IG g,E e){return switch(e){
      case E.X x->{
        var a=g.adapted(x.name);var z=x.t;if(a.equals(z))yield x;var o=g.get(x.name);
        var t=z.und()?null:o.und()?z
          :o instanceof R(var aRc,var aC)&&z instanceof R(var bRc,var bC)&&aC.name.equals(bC.name)?new R(aRc==null?bRc:bRc==null?aRc:lowerCap(aRc,bRc),aC)
          :o instanceof RX y&&z instanceof RX(var bRc,var bX)&&y.x.equals(bX)?y.rc(lowerCap(y.r,bRc)):null;
        if(t!=null)g.fs.get(g.at(x.name)).vars.put(x.name,t);yield x.t(meet(a,z));
      }
      case Literal l->literal(b,g,l);
      case Call c when c.written||c.r!=null->call(b,g,c);
      case Call c->{
        var ee=solve(b,g,c.e);
        var m=ee.t() instanceof R w?signature(w,c.name,null,c.t.erc()):null;if(m==null)yield c.children(ee,solve(b,g,c.es));
        var types=qs(m.mb.size());
        yield new Call(ee,c.name,m.r,types,expect(c.es,m,types),meet(c.t,m.inst(m.ret,types)),false);
      }
    };}
    M lookup(R w,MN name,RC favorite,RC hint){
      var d=from(w.c.name);if(d==null)return null;var ms=filter(d.ms,m->m.s.m.equals(name));
      var r=noH(or(w.r==iso?hint:w.r,imm));
      var order=favorite!=null?list(favorite):list(r==iso?imm:r,read,imm,mut);
      return ms.size()==1&&favorite==null?ms.get(0):find(map(order,o->find(ms,m->m.s.r==o)),Objects::nonNull);
    }
    MS signature(R w,MN name,RC favorite,RC hint){var d=from(w.c.name);var m=lookup(w,name,favorite,hint);
      return m==null?null:new MS(m.s.r,push(B.v(d.b),B.v(m.s.b)),d.b,w.c.types,m.s.b,m.s.types,m.s.t);
    }
    static RC lowerCap(RC a,RC b){a=noH(a);b=noH(b);return a==b||b==read?a:a==read?b:iso;}
    static boolean instance(Literal l){return l.anon&&all(l.ms,m->m.e==null);}
    E call(List<B>b,IG g,Call c){var e=solve(b,g,c.e);MS m;
      if(!(e.t() instanceof R w)||(m=signature(w,c.name,c.r,null))==null)return c.children(e,solve(b,g,c.es));
      var n=m.cas.size();var bs=push(m.cb,m.mb);var all0=normalize(b,bs,infer(c,m,c.es,false));var m0=m.arguments(all0.subList(0,n));
      var es=solve(b,g,expect(c.es,m0,all0.subList(n,all0.size())));
      var all=normalize(b,bs,infer(c,m,es,true));var ts=all.subList(0,n);
      var y=all.subList(n,all.size());e=meet(e,w.withTs(ts));var m1=m.arguments(ts);
      return new Call(e,c.name,or(c.r,m1.r),y,expect(es,m1,y),meet(c.t,m1.inst(m1.ret,y)),c.written);
    }
    List<T>arguments(MS m,List<E>es,boolean literals){
      var is=range(es.size()).filter(i->!literals||es.get(i) instanceof Literal l&&!instance(l)).boxed().toList();
      Function<Integer,List<T>>ref=i->refine(m.v,m.ps.get(i),es.get(i).t());
      var lower=map(filter(is,i->!(m.ps.get(i) instanceof R)),ref);var exact=map(filter(is,i->m.ps.get(i) instanceof R),ref);
      return meet(push(lower.stream().reduce(qs(m.v.size()),(a,b)->zip(a,b,this::join)),exact));
    }
    List<T>infer(Call c,MS m,List<E>es,boolean use){var y=MS.fixTargs(c.y,m.mb.size());var ret=refine(m.v,m.ret,c.t);
      return Stream.of(push(m.cas,c.written?y:qs(m.mb.size())),m.ret instanceof R?ret:qs(m.v.size()),arguments(m,es,true),meet(List.of(push(m.cas,y),use?arguments(m,es,false):qs(m.v.size()),ret)))
        .reduce((p,q)->zip(p,q,(a,b)->a.tv()&&!(a instanceof R(var r,_)&&r==null)?a:b)).get();
    }
    R self(Literal l){return l.r==null?null:l.self(l.r);}
    E literal(List<B>b,IG g,Literal l){var sp=self(l);if(!l.expanded){
      l=l.t(!l.anon?sp:l.cs.size()==1?new R(l.r,l.cs.get(0)):or(sp,l.t));if(!(l.t instanceof R(_,var c)))return l;
      l=l.anon&&!c.name.equals(l.name)?implement(l,c,b):expand(l,true);
    }
      if(!(l.t instanceof R w))return l;var res=new Vector<M>();var types=w.c.types;for(var mi:l.ms){
        var k=bound(w,types);var next=mi.e==null?header(k,mi):method(b,g,l,sp,k,mi);
        types=meet(types,next.types);res.add(next.m);
      }
      if(res.equals(l.ms)&&types.equals(w.c.types))return commit(g,b,l,w);var t=bound(w,types);
      return commit(g,b,l.header(l.cs,res,true).t(t),t);
    }
    E commit(IG g,List<B>b,Literal l,R w){var name=l.name;
      if(!w.tv()||!all(l.ms,m->m.s.t.tv()&&all(m.s.types,T::tv))||cache.containsKey(name))return l;
      var bs=cat(methodFree(g,l.ms),supFree(l.cs),w.ftv()).distinct().map(x->B.get(b,x)).toList();var name1=name.arity(bs.size());
      var cap=noH(or(l.r,w.r));var instance=instance(l);
      var own=w.c.name.equals(name);no(!own&&!w.c.name.visible()&&!w.c.name.pk().equals(p.name));
      var cs=Core.distinct(bs,own?parents(w.c):push(w.c,parents(w.c)));
      l=new Literal(cap,name1,bs,cs,l.self,map(l.ms,mi->mi.o(name,name1)),w,l.anon,l.expanded);if(!instance)magic(l,cs);
      if(own)l=l.t(self(l));register(l);var s=sup(w,widen);return!instance?l:l.t(new R(cap,s!=null&&s.c.types.get(0) instanceof R(_,var c)?c:w.c));
    }
    record TSM(List<T>types,M m){}
    TSM header(R w,M m){
      var s=m.s;var omh=lookup(w,s.m,s.r,null);if(omh==null)return new TSM(w.c.types,m);
      var Xs=B.v(from(w.c.name).b);var byArg=zip(omh.s.types,s.types,(t,it)->refine(Xs,t,it));var v=bound(w,zip(w.c.types,meet(push(byArg,refine(Xs,omh.s.t,s.t))),this::keep));
      var h=signature(v,s.m,s.r,null);var x=vars(s.b);
      return new TSM(erase(v.c.types,B.v(s.b)),m.signature(s.types(map(h.ps,p->h.inst(p,x)),h.inst(h.ret,x))));
    }
    TSM method(List<B>b,IG g,Literal l,R sp,R w,M m){var bs=l.anon?b:l.b;
      g.fs.add(new IG.Frame(m.s.r,bs,new HashMap<>()));
      g.declare(l.self,sp==null?u:new R(sp.r==null?null:sp.r.mutable(),sp.c));
      g.fs.add(new IG.Frame(m.s.r,bs,new HashMap<>()));g.declare(m);
      var e=solve(push(bs,m.s.b),g,meet(m.e,m.s.t));
      var args=zip(m.v,m.s.types,(x,t)->meet(t,g.get(x)));g.fs.removeLast();
      g.fs.removeLast();var h=header(w,m.signature(m.s.types(args,meet(m.s.t,e.t()))));var s=h.m.s;
      return new TSM(h.types,new M(s,m.v,meet(e,s.t)));
    }
    T keep(T decided,T body){
      if(variable(decided)!=null&&variable(decided).equals(variable(body))&&!(decided instanceof RX&&decided.erc()==iso))return decided;
      if(!(decided instanceof R(var aRc,var aC)&&body instanceof R b))return meet(decided,body);
      if(!aC.name.equals(b.c.name)){var s=sup(b,aC.name);return s==null?decided:keep(decided,s);}
      return b.with(or(aRc,b.r),zip(aC.types,b.c.types,this::keep));
    }
    List<T>erase(List<T>types,List<String>mb){
      return mb.size()==0?types:map(types,t->t instanceof R w?bound(w,erase(w.c.types,mb)):mb.contains(variable(t))?u:t);
    }
    List<T>refine(List<String>v,T t,T a){
      return a.und()?qs(v.size()):switch(t){
        case X x->{var n=v.indexOf(x.name);yield seq(v.size(),i->i==n?a:u);}
        case RX(_,var x)->refine(v,x,switch(a){
          case RX(_,var p)->p;case RI(var p)->p;case R(_,var c)->new R(null,c);default->a;
        });
        case RI(var x)->refine(v,x,a instanceof RI(var p)?p:a);case R w->propagate(v,w,a);default->qs(v.size());
      };
    }
    R sup(R src,N target){var c=find(parents(src.c),ci->ci.name.equals(target));return c==null?null:new R(src.r,c);}
    List<T>propagate(List<String>v,R r,T a){
      if(!(a instanceof R cc))return qs(v.size());var c=r.c;if(!cc.c.name.equals(c.name)){var up=sup(cc,c.name);
        if(up!=null)return propagate(v,r,up);var down=sup(r,cc.c.name);return down==null?qs(v.size()):propagate(v,down,a);
      }
      var res=zip(c.types,cc.c.types,(t,ti)->t instanceof R rr&&!(ti instanceof R ci&&ci.c.name.equals(rr.c.name))?qs(v.size()):refine(v,t,ti));
      return res.size()==0?qs(v.size()):meet(res);
    }
    E ascribe(E arg,T expected,MN called){
      if(!(expected instanceof R exp))return arg;
      return switch(arg){
        case Call c->c.children(ascribe(c.e,expected,c.name),c.es);
        case Literal l->l.expanded||!l.anon||l.cs.size()>0||!l.t.und()?arg:called==null||implementable(exp.c.name)&&!any(l.ms,m->called.equals(m.s.m)&&m.s.t!=u&&!any(m.s.types,t->t==u))?l.t(new R(exp.r,new C(exp.c.name,qs(exp.c.types.size())))):new Literal(imm,l.name,l.b,l.cs,l.self,l.ms,l.self(imm),true,false);
        default->arg;
      };
    }
    boolean implementable(N head){
      var d=from(head);return d!=null&&(head.pk().equals(p.name)||head.visible()&&!has(d.cs,sealed))&&TS.inst(d);
    }
    static T normalize(T t,Set<RC>al){
      if(al.size()==1)return t.rc(al.iterator().next());
      return t instanceof R(var r,var c)&&(r==null||r==iso&&!al.contains(iso))?new R(al.contains(imm)?null:read,c):t;
    }
    static List<T>normalize(List<B>scope,List<B>b,List<T>types){
      return zip(types,b,(ti,bi)->variable(ti)==null||B.get(scope,variable(ti)).caps.equals(bi.caps)?normalize(ti,bi.caps):ti);
    }
    R bound(R w,List<T>types){
      var d=from(w.c.name);return w.withTs(d==null?types:zip(types,d.b,(ti,bi)->normalize(ti,bi.caps)));
    }
  }
  record Core(List<B>ctx,Methods meths){
    E core(E exp,E orig){return switch(exp){
      case E.X x->x.t(u);
      case Literal le->literal(le,(Literal)orig);
      case Call e->{var o=(Call)orig;var types=o.y.size()==0?e.y:o.y;
        yield new Call(core(e.e,o.e),e.name,or(e.r,imm),seq(types.size(),i->targ(e,types.get(i),i)),zip(e.es,o.es,this::core),u,false);
      }
    };}
    T targ(Call e,T t,int i){
      var m=t==u&&e.e.t() instanceof R w?meths.lookup(w,e.name,e.r,null):null;if(m==null)return norm(fillVoid(t));
      return voidT(m.s.b.get(i).caps.iterator().next());
    }
    static T voidT(RC r){return new R(r,new C(voidName,list()));}
    static T fillVoid(T t){no(t instanceof Amb);return t==u?voidT(imm):t instanceof R w?w.withTs(map(w.c.types,Core::fillVoid)):t;}
    Literal literal(Literal e,Literal o){
      no(!(e.t instanceof R)&&!e.t.und());var b=e.anon&&e.b.size()==0?cat(supFree(e.cs),methodFree(new IG(),push(e.ms,o.ms))).distinct().map(x->B.get(ctx,x)).toList():e.b;
      var name=e.name.arity(b.size());
      var inner=e.anon?with(b):new Core(b,meths);
      return new Literal(or(e.r,imm),name,b,map(distinct(inner.ctx,push(o.cs,e.cs)),Frontend::normC),e.self,map(e.ms,me->inner.m(me,me.e==null?me:o.ms.get(me.s.idx)).o(e.name,name)),u,e.anon,false);
    }
    static List<C>distinct(List<B>b,List<C>cs){var res=new Vector<C>();
      for(var c:cs){if(!any(res,r->TS.equivalent(b,fill(new R(imm,r)),fill(new R(imm,c)))))res.add(c);}return res;
    }
    Core with(List<B>b){return new Core(push(ctx,b).stream().distinct().toList(),meths);}
    M m(M e,M o){var s=merge(e.s,o.s);return new M(s,e.v,e.e==null?null:with(s.b).core(e.e,o.e));}
    static S merge(S inf,S usr){
      return new S(or(usr.r,or(inf.r,imm)),required(or(usr.m,inf.m)),or(usr.b,or(inf.b,list())),
        zip(usr.types,inf.types,(y,i)->norm(y==u?i:y)),norm(usr.t==u?inf.t:usr.t),required(or(usr.o,inf.o)),usr.abs,usr.idx);
    }
  }
  record G(G tail,String name,T t){
    static final G empty=new G(null,null,null);
    G add(String name,T t){return new G(this,name,t);}
    G map(UnaryOperator<T>f){return this==empty?this:new G(tail.map(f),name,t==null?null:f.apply(t));}
    T bind(String x){return this==empty?null:name.equals(x)?t:tail.bind(x);}
  }
  record MT(RC r,List<T>types,T t){}
  static final RC[]reading={imm,iso,readH,iso,mutH,readH},flexy={imm,iso,imm,iso,mutH,readH},hyg={imm,mutH,readH,iso,mutH,readH},strong={imm,iso,imm,iso,iso,imm};
  record TS(Function<N,Literal>decs){
    static void check(List<Literal>tops,Map<N,Literal>other){var map=new HashMap<N,Literal>();
      tops.forEach(t->collect(t,map));var sys=new TS(n->from(n,map::get,other));tops.forEach(l->sys.check(G.empty,l,has(l.cs,cf)?imm:l.r));
    }
    static void collect(E e,HashMap<N,Literal>map){if(e instanceof Literal l)map.put(l.name,l);e.children().forEach(c->collect(c,map));}
    boolean kinded(List<B>b,T t,Set<RC>al){
      return al.containsAll(kinds(b,t))&&(!(t instanceof R(_,var c))||all(zip(c.types,decs.apply(c.name).b,(ti,p)->kinded(b,ti,p.caps)),v->v));
    }
    void kind(List<B>b,T t,Set<RC>al){no(!kinded(b,t,al));}
    static Set<RC>kinds(List<B>b,T t){return switch(t){
      case R(var r,_)->caps(or(r,read));case RX(var r,_)->caps(r);case X(var x)->B.get(b,x).caps;
      case RI(var x)->{var caps=kinds(b,x);
        yield ii.containsAll(caps)?caps(imm):caps(mut,mutH,read,readH).containsAll(caps)?caps(read):caps(read,imm);
      }default->throw new Fail();
    };}
    boolean sub(List<B>b,T a,T z){return a.equals(z)
      ||z instanceof RI(var q)&&q.equals(a)&&kinded(b,a,plain)
      ||shape(b,a,z)
      ||a instanceof R(var rc1,var c1)&&any(decs.apply(c1.name).cs,ci->sub(b,rename(new R(rc1,ci),B.v(decs.apply(c1.name).b),c1.types),z));
    }
    List<T>type(List<B>b,G g,E e,List<T>rs){return switch(e){
      case E.X x->reqs(b,required(g.bind(x.name)),rs);
      case Literal l->literal(b,g,l,rs);case Call c->call(b,g,c,rs);
    };}
    static boolean inst(Literal l){return l.self.equals("this")||has(l.cs,cf);}
    static long count(String x,E e,boolean active){
      return e instanceof E.X v?v.name.equals(x)?1:0:active&&e instanceof Literal?0:e.children().mapToLong(c->count(x,c,active)).sum();
    }
    List<T>reqs(List<B>b,T got,List<T>rs){
      if(rs.size()==0)return list(got);return map(rs,r->sub(b,got,r)?got:null);
    }
    List<T>literal(List<B>bs1,G g,Literal l,List<T>rs){
      var gf=g.map(t->has(l.cs,cf)||!t.ftv().allMatch(B.v(l.b)::contains)?null:t);var r=(l.r.ro()&&!any(l.ms,m->m.s.abs&&m.s.r==mut)||l.r==mut||l.r==mutH)&&cf(l.b,gf,l)?iso:l.r;
      no(any(l.ms,m->(m.s.abs||m.e!=null&&!inst(l))&&m.s.abs==(m.s.r!=mut||!r.ro())));
      var t=l.self(r);kind(bs1,t,allRC);check(gf.map(x->!kinded(l.b,x,plain)||r.ii()&&!kinded(l.b,x,ii)?null:x),l,l.r.mutable());
      no(any(rs,x->!(x instanceof R)));return reqs(bs1,t,rs);
    }
    static boolean cf(List<B>b,G g,E e){
      return e instanceof E.X x?g.bind(x.name)==null||all(kinds(b,g.bind(x.name)),RC::ii):e.children().allMatch(c->cf(b,g,c));
    }
    void check(G g,Literal l,RC self){
      if(has(l.cs,identity)){var m=l.ms.get(0);no(!switch(m.e){
        case null->true;
        case E.X(var name,_)->name.equals(m.v.get(0));
        case Call c->c.e instanceof E.X(var recv,_)&&recv.equals(m.v.get(0))&&c.name.equals(new MN(".as",1))
          &&m.s.types.get(0) instanceof R(_,var cc)&&has(decs.apply(cc.name).cs,container);
        default->false;
      });}
      var sources=new Vector<S>();for(var parent:l.cs){kind(l.b,new R(imm,parent),allRC);var sup=decs.apply(parent.name);no(!inst(sup));for(var m:sup.ms){
        if(!m.s.o.equals(sup.name))continue;var s=m.s;var canonical=canonical(l,s.m,s.r).b;
        sources.add(s.subst(canonical,B.v(push(s.b,sup.b)),push(vars(canonical),parent.types)));
      }}
      for(var m:l.ms){if(m.s.o.equals(l.name))sources.add(m.s);}
      group(sources,s->new Key(s.r,s.m)).forEach((k,sigs)->{
        var chosen=canonical(l,k.name,k.r);var ctx=push(l.b,chosen.b);for(var s:sigs)
          no(zip(chosen.types,s.types,(p,q)->!same(ctx,p,q)||!sub(ctx,q,p)).contains(true)||!same(ctx,chosen.t,s.t)||!sub(ctx,chosen.t,s.t));
      });
      var g1=g.add(l.self,l.self(self));for(var m:l.ms){var g2=g1.map(t->IG.adapt(t,m.s.r,l.b));
        var bs=push(l.b,m.s.b);push(m.s.types,m.s.t).forEach(t->kind(bs,t,allRC));if(m.e==null)continue;
        for(int i=0;i<m.v.size();i++){var x=m.v.get(i);var ti=m.s.types.get(i);g2=g2.add(x,ti);no(!kinded(bs,ti,caps(mut,read,mutH,readH,imm))&&count(x,m.e,true)>0&&count(x,m.e,false)!=1);}
        no(type(bs,g2,m.e,list(m.s.t)).get(0)==null);
      }
    }
    static S canonical(Literal l,MN name,RC r){return required(find(l.ms,m->m.s.m.equals(name)&&m.s.r==r)).s;}
    static boolean shape(List<B>b,T a,T z){
      return equivalent(b,a.rc(mut),z.rc(mut))&&all(kinds(b,a),r1->all(kinds(b,z),r1::sub));
    }
    static boolean same(List<B>b,T p,T q){return(p instanceof RI)==(q instanceof RI)&&p.erc()==q.erc()||equivalent(b,p,q);}
    static boolean equivalent(List<B>b,T p,T q){
      return p.equals(q)||(p instanceof R(var aRc,var aC)&&q instanceof R(var bRc,var bC)?aRc==bRc&&aC.name.equals(bC.name)&&all(zip(aC.types,bC.types,(s,t)->equivalent(b,s,t)),v->v)
        :p.rc(imm) instanceof RX(_,var x)&&p.rc(imm).equals(q.rc(imm))&&B.get(b,x.name).caps.size()==1&&kinds(b,p).equals(kinds(b,q)));
    }
    List<T>call(List<B>b,G g,Call c,List<T>rs){
      if(!(type(b,g,c.e,list()).get(0) instanceof R h))throw new Fail();var d=decs.apply(h.c.name);
      var s=canonical(d,c.name,c.r);
      no(s.b.size()!=c.y.size());for(int i=0;i<c.y.size();i++)kind(b,c.y.get(i),s.b.get(i).caps);
      var v=B.v(push(d.b,s.b));var ts0=push(h.c.types,c.y);
      var base=new MT(s.r,rename(s.types,v,ts0),rename(s.t,v,ts0));
      var app=cat(Stream.of(base,apply(b,base,flexy,flexy,-1,flexy),apply(b,base,strong,strong,-1,strong),apply(b,base,reading,reading,-1,hyg),apply(b,base,hyg,flexy,-1,hyg)),
        range(base.types.size()).mapToObj(i->apply(b,base,flexy,flexy,i,hyg))).distinct().filter(m->h.r.sub(m.r)).toList();no(app.size()==0);
      var possible=new Vector<>(app);range(c.es.size()).forEach(i->{
        var reqs=app.stream().map(m->m.types.get(i)).distinct().toList();var got=type(b,g,c.es.get(i),reqs);
        no(all(got,Objects::isNull));possible.removeIf(m->got.get(reqs.indexOf(m.types.get(i)))==null);
      });
      no(possible.size()==0);return rs.size()==0?list(best(b,possible)):map(rs,req->best(b,filter(possible,m->sub(b,m.t,req))));
    }
    T best(List<B>b,List<MT>ms){var types=map(ms,MT::t);return find(types,p->!any(types,q->!q.equals(p)&&sub(b,q,p)));}
    static MT apply(List<B>d,MT m,RC[]receiver,RC[]args,int at,RC[]result){
      return new MT(receiver[m.r.ordinal()],seq(m.types.size(),j->adapt(d,m.types.get(j),j==at?hyg:args,(p,q)->q.sub(p))),adapt(d,m.t,result,RC::sub));
    }
    static T adapt(List<B>d,T t,RC[]mode,BiPredicate<RC,RC>le){
      if(t.erc()!=null)return t.rc(mode[t.erc().ordinal()]);var x=variable(t);if(x==null)return t;
      var caps=EnumSet.copyOf(map(B.get(d,x).caps,(RC r)->t instanceof RI?r.ri():r));if(all(caps,r->mode[r.ordinal()]==r))return t;
      var up=Stream.of(RC.values()).filter(p->all(caps,c->le.test(mode[c.ordinal()],p))).toList();return new RX(find(up,p->all(up,o->le.test(p,o))),new X(x));
    }
  }
}
