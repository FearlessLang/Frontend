package compact;
import static compact.Frontend.K.*;
import static compact.Frontend.RC.*;
import static compact.Frontend.Mode.*;
import static compact.Util.*;
import compact.Frontend.T.*;
import compact.Frontend.E.Call;
import compact.Frontend.E.Type;
import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
public final class Frontend{
  @SuppressWarnings("serial")public static final class Fail extends RuntimeException{}
  static void no(boolean b){if(b)throw new Fail();}
  public static Object parse(String input){return new Parser(new Names(list(),list(),list(),null),tokens(input)).group(Parser::file);}
  public static List<Literal>compile(String pk,Map<String,String>override,Map<String,String>files,List<Literal>lits){
    var other=lits.stream().collect(Collectors.toMap(Literal::name,d->d));var raw=new TreeMap<String,File>();
    files.forEach((path,content)->raw.put(path,(File)parse(content)));
    var heads=filter(raw.keySet(),p->p.matches("(.*/)?_rank_[^/]*\\.[^/]*"));
    no(heads.size()!=1);var head=raw.get(heads.get(0));
    no(any(raw.values(),f->f!=head&&f.maps.size()+f.uses.size()>0));
    var ds=flat(raw.values(),f->f.decs.stream());var uses=map(head.uses,File.Use::out);
    var names=flat(ds,d->d.owner.decs.stream());no(dup(names));var strings=map(names,N::s);
    no(!Collections.disjoint(strings,uses));no(ds.stream().flatMap(d->d.owner.gen.used.stream()).anyMatch(x->strings.contains(x)||uses.contains(x)));
    var map=new HashMap<>(override);for(var u:head.uses){var p=map.getOrDefault(u.in.pk(),u.in.pk());
      var in=p+"."+u.in.simple();map.put(u.out,in);
      var dom=p.equals(pk)?names.stream().map(n->n.qualify(pk)):other.keySet().stream();
      no(dom.noneMatch(e->e.s.equals(in)));
    }var ctx=new Methods(new Pkg(pk,map,ds,new HashSet<>(names)),other);
    var res=ctx.steps(ctx.headers(lower(ctx)));TS.check(res,other);return res;
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
  public record MN(String s,int arity){MN arity(int arity){return new MN(s,arity);}}
  public record B(String x,Set<RC>caps){
    static List<String>v(List<B>b){return map(b,B::x);}
    static B get(List<B>b,String name){return find(b,e->e.x.equals(name));}
  }
  enum K{
    Ws("\\s+"),LC("//[^\\n]*"),BC("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"),
    Arrow("->"),LP("\\("),RP("\\)"),LB("\\{"),RBId("\\}[A-Za-z0-9_]+'*"),RB("\\}"),
    LA("(?<=[A-Za-z0-9_'"+K.op+"])(?<!\\*/)\\["),RA("\\]"),
    Hole("_"),Comma(","),Semi(";"),Implicit("::"),Colon(":"),Eq("="),Quote("'"),RIcap("read/imm"),Cap("readH|mutH|imm|iso|read|mut"),
    SF("[+-]"+K.flt),UF(K.flt),SI("[+-]"+K.nat),UI(K.nat),Str("\"[^\"\\n]*\""),Raw("`[^`\\n]*`"),
    Dot("\\._*[a-z]"+K.id),Up("(?:"+K.pk+"\\.)?_*[A-Z]"+K.id),
    Low("_*[a-z]"+K.id),Bad("'(?:(?!//|/\\*)[^'\\n\"`])*'(?![_a-z])"),Op("(?:(?!/\\*|\\*/|//)["+K.op+"])+"),
    End(""),Start(""),Curly(""),Square(""),Round("");
    static final String pk="(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*",id="[A-Za-z0-9_]*'*",
      op="\\\\/#*\\-+%<>=!&^~?|",nat="[0-9](?:[0-9_]*[0-9])?",flt=nat+"\\."+nat+"(?:[eE][+-]?"+nat+")?(?:soft)?";
    final Pattern p;
    K(String regex){p=Pattern.compile(regex);}
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
      var t=new Token(best,s.substring(i,i+len),list());i+=len;if(t.is(Ws,LC,BC))continue;
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
    int arity(){return s.ps.size()+(implicit?1:0);}
  }
  static boolean implicit(P e){return switch(e){
    case P.X _,P.Typed _,P.Declared _,P.Lit _->false;case P.Implicit _->true;
    case P.Call c->implicit(c.e)||any(c.es,Frontend::implicit);
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
  record File(List<String>maps,List<Use>uses,List<Declaration>decs){record Use(N in,String out){}}
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
    boolean peek(Predicate<Token>p){return!end()&&p.test(tokens.get(index));}
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
      var c=name();if(!see(Square))return new C(c,list());var types=items(comma,Parser::type);
      return new C(c.arity(types.size()),types);
    }
    N name(){var s=take(heads).content;
      no(names.Xs.contains(s)||names.hid.contains(s));var res=new N(s,0);no(!res.pk().isEmpty()&&!res.visible());return res;
    }
    T type(){
      if(fwd(see(RIcap)))return new RI(variable(false));var r=optCap();
      if(peek(t->t.is(heads)&&!names.Xs.contains(t.content)))return new R(or(r,imm),constructor());
      var res=variable(false);return r==null?res:new RX(r,res);
    }
    X variable(boolean mustNew){
      var c=take(Up,"[^.]*");no(mustNew?names.Xs.contains(c)||names.hid.contains(c):!names.Xs.contains(c));return new X(c);
    }
    P post(P receiver){
      if(see(SF,SI)){var num=take().content;
        var lit=new P.Typed(imm,new C(new N(num.substring(1),0),list()),null);
        return new P.Call(receiver,num.substring(0,1),null,null,list(lit));
      }
      var m=take(Dot,Op).content;var sq=see(Square)?group(Parser::arguments):null;
      if(see(Round)){var es=items(Parser::exprEnd,Parser::expr);return new P.Call(receiver,m,sq,null,es);}
      var xpat=see(Low,Curly)&&see(1,Eq)?pattern():null;if(xpat!=null)take(Eq);
      if(end()||see(Dot,Op,Colon)){no(xpat!=null);return new P.Call(receiver,m,sq,xpat,list());}
      var atom=atom();var v=xsOf(xpat).toList();fresh(v);
      no(xpat instanceof Pat.Des&&v.size()>31);names=names.add(v,list());
      if(xpat==null)return new P.Call(receiver,m,sq,xpat,list(atom));
      return new P.Call(receiver,m,sq,xpat,list(atom,posts(post(new P.X("")))));
    }
    Pat pattern(){if(see(Low,Hole))return new Pat.Name(binder().name);return group(Parser::destruct);}
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
    P.X binder(){var x=take(Low,Hole).content;no(names.v.contains(x));return new P.X(x);}
    P.Lit literal(boolean top){
      no(tokens.get(limit).is(RBId));var self=fwd(see(Quote))?binder().name:top?"this":"_";
      no(top&&!self.equals("this"));if(!self.equals("_"))names=names.add(list(self),list());
      var ms=by(p->p.so(1,Semi),p->p.method(top));
      var ns=map(filter(ms,m->m.s.m!=null),m->new Key(m.s.r,new MN(m.s.m,m.arity())));no(dup(ns));
      no(any(ns,nn->nn.r==null&&any(ns,o->o.name.equals(nn.name)&&o.r!=null)));
      no(dup(map(filter(ms,m->m.s.m==null),PM::arity)));return new P.Lit(self,ms);
    }
    Stream<String>xsOf(Pat xp){return Stream.ofNullable(xp).flatMap(Pat::names).filter(x->!x.equals("_"));}
    void fresh(List<String>v){no(dup(v)||any(v,names.v::contains));}
    PM body(PS s){
      var v=flat(s.ps,p->xsOf(p.xp));fresh(v);
      names=names.add(v,B.v(or(s.b,list())));var m=new PM(s,whole(Parser::expr));
      no(any(s.ps,p->p.xp instanceof Pat.Des)&&v.size()+(m.implicit?1:0)>32);return m;
    }
    PM method(boolean top){
      var m=prefix(p->p.so(1,Arrow),Parser::signature);if(m!=null)return body(m);
      var sig=see(Dot,Op)||see(Cap)&&see(1,Dot,Op);if(!sig)return new PM(bare,whole(Parser::expr));
      var s=signature();no(!top);return new PM(s,null);
    }
    PS signature(){
      var r=optCap();no(r!=null&&(r.isH()||r==iso));
      var m=see(Dot,Op)?take().content:null;var b=see(Square)?bounds(true):null;
      names=names.add(list(),B.v(or(b,list())));
      var ps=see(Round)?items(comma,Parser::parameter):see(Colon)?List.<Par>of():by(comma,Parser::parameter);
      var t=fwd(see(Colon))?type():u;no(!end());var v=flat(ps,p->xsOf(p.xp));
      no(dup(v));names.owner.vars.used.addAll(v);return new PS(r,m,b,ps,t);
    }
    Par parameter(){
      var x=see(Low,Hole,Curly)?pattern():null;
      var p=new Par(x,x==null?type():fwd(see(Colon))?type():u);no(!end());return p;
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
      var b=see(Square)?bounds(top):List.<B>of();var Xs=B.v(b);var outer=names;var owner=top?new Owner():names.owner;
      names=new Names(names.v,list(),push(names.hid,names.Xs),owner).add(list(),Xs);c=c.arity(Xs.size());owner.decs.add(c);take(Colon);
      var cs=required(prefix(p->p.so(2,Curly),p->p.by(comma,Parser::constructor)));no(dup(cs));
      var l=group(p->p.literal(top));names=outer;return new Declaration(c,b,cs,l,owner);
    }
    File file(){
      var maps=new Vector<String>();var uses=new Vector<File.Use>();Function<Parser,Object>header=p->{
        if(!p.see(Low))return null;no(!p.tokens.get(--p.limit).is(Semi));return p.by(q->q.so(1,Semi),q->q.directive(maps,uses));
      };front(Parser::headEnd).whole(header);
      var ds=by(p->p.so(0,Curly),p->p.declaration(true));return new File(maps,uses,ds);
    }
    String take(K kind,String regex){var s=take(kind).content;no(!s.matches(regex));return s;}
    Object directive(Vector<String>maps,Vector<File.Use>uses){
      if(fwd(peek(t->t.content.equals("map")))){
        var in=take(Low,K.pk);take(Low,"as");take(Low,K.pk);
        take(Low,"in");var key=in+" "+take(Low,K.pk);no(maps.contains(key));maps.add(key);
      }else{
        take(Low,"use");var a=name();take(Low,"as");
        var z=take(Up,"[^.]*");no(any(uses,u->u.in.equals(a)||u.out.equals(z)));
        uses.add(new File.Use(a,z));
      }no(!end());return null;
    }
    int exprEnd(){var inColon=false;while(!end()){
      var t=take();if(t.is(Comma)&&!inColon)return 1;if(!t.is(Square,Comma,Up))inColon=false;
      if(t.is(Colon))inColon=true;
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
      var res=new N(pk+"."+fresh(hint.simple(),"ABCDEFGHJKMNPQRSTUVWXYZ",top,list(reserved)),arity);owners.put(res,owners.get(hint));return res;
    }
    boolean available(N owner,String x,List<String>scope){return!owners.get(owner).gen.used.contains(x)&&!top.used.contains(x)&&!scope.contains(x);}
    String generic(N owner,String hint,List<String>siblings){
      var cand=fresh(hint,"ABCDEFGHJKMNPQRSTUVWXYZ",owners.get(owner).gen,list(top.used,siblings));reserved.add(cand);return cand;
    }
    String variable(N owner,String hint){return fresh(hint,"abcdefghjkmnpqrstuvwxyz",owners.get(owner).vars,list());}
    static String fresh(String hint,String alphabet,Scope s,List<Collection<String>>checks){
      var base=hint.replaceAll("[^A-Za-z0-9]","").replaceFirst("(?<=.{4}).*","");for(int n=s.seq.getOrDefault(base,1);;n+=1){
        var sb=new StringBuilder();for(int k=n;k>0;k=(k-1)/alphabet.length())sb.append(alphabet.charAt((k-1)%alphabet.length()));
        var cand="_"+sb.reverse()+base;if(s.used.contains(cand)||any(checks,e->e.contains(cand)))continue;
        s.used.add(cand);s.seq.put(base,n+1);return cand;
      }
    }
  }
  static final N str=new N("base.Str",0),nat=new N("base.Nat",0),integer=new N("base.Int",0),floating=new N("base.Float",0),
    widen=new N("base.WidenTo",1),sealed=new N("base.Sealed",0),cf=new N("base.CaptureFree",0),identity=new N("base.BaseId",2),
    container=new N("base.BaseContainer",1),voidName=new N("base.Void",0);
  static Set<RC>caps(RC first,RC...rest){return EnumSet.of(first,rest);}
  static final Set<RC>ii=caps(iso,imm),plain=caps(iso,imm,mut,read),allRC=EnumSet.allOf(RC.class);
  static boolean has(List<C>cs,N magic){return any(cs,c->c.name.equals(magic));}
  static boolean primitive(String name){return"+-1234567890\"`".contains(name.substring(0,1));}
  static Literal from(N n,Function<N,Literal>map,Map<N,Literal>other){
    var res=map.apply(n);if(res==null)res=other.get(n);
    if(res!=null||!n.pk().equals("base")||!primitive(n.simple()))return res;var s=n.simple();
    var lit=s.startsWith("`")||s.startsWith("\"")?str:matches(s,UI)?nat:matches(s,SI)?integer:floating;
    var sup=from(lit,map,other);var ms=map(sup.ms,m->m.signature(new S(m.s.r,m.s.m,m.s.b,m.s.types,m.s.t,n,false,m.s.idx)));
    return new Literal(imm,n,list(),push(new C(lit,list()),sup.cs),"this",ms,true);
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
    record C(N name,List<T>types){int depth(){return 1+types.stream().mapToInt(T::depth).max().orElse(1);}}
    record R(RC r,C c)implements T{
      public R{no(c.depth()>1000);}R withTs(List<T>types){return with(r,types);}
      R with(RC r,List<T>types){return new R(r,new C(c.name,types));}
      public boolean tv(){return all(c.types,T::tv);}public int depth(){return c.depth();}
      public RC erc(){return r;}
    }
    enum U implements T{Instance}
    record Amb(List<T>cs)implements T{}
    default boolean und(){return this==u||this instanceof Amb;}
    default T rc(RC r){return und()?this:this instanceof R w?new R(r,w.c):new RX(r,new X(variable(this)));}
    default Stream<String>ftv(){return this instanceof R w?typeFree(w.c.types):Stream.ofNullable(variable(this));}
    default T ri(){return switch(this){
      case X x->new RI(x);case RI _->this;
      case R(var r,var c)->new R(r==null?null:r.ri(),c);case RX(var r,var x)->new RX(r.ri(),x);case U _,Amb _->this;
    };}
  }
  public sealed interface E{
    T t();E t(T t);
    default Stream<E>children(){return switch(this){
      case X _,Type _->Stream.of();case Literal l->l.ms.stream().flatMap(m->Stream.ofNullable(m.e));case Call c->cat(Stream.of(c.e),c.es.stream());
    };}
    record X(String name,T t)implements E{
      X(String name){this(name,u);}public E t(T t){return new X(name,t);}
    }
    record Type(R type,T t)implements E{
      Type(R type){this(type,u);}public E t(T t){return new Type(type,t);}
    }
    record Call(E e,MN name,RC r,List<T>y,List<E>es,T t,boolean written)implements E{
      Call(E e,MN name,RC r,List<T>y,List<E>es,boolean written){this(e,name,r,y,es,u,written);}
      Call children(E e,List<E>es){return new Call(e,name,r,y,es,t,written);}
      public Call t(T t){return new Call(e,name,r,y,es,t,written);}
    }
  }
  public record Literal(RC r,N name,List<B>b,List<C>cs,String self,List<M>ms,T t,boolean anon,boolean expanded)implements E{
    Literal(RC r,N name,List<B>b,List<C>cs,String self,List<M>ms,boolean anon){this(r,name,b,cs,self,ms,u,anon,false);}
    public Literal t(T t){return new Literal(r,name,b,cs,self,ms,t,anon,expanded);}
    Literal header(List<C>cs,List<M>ms,boolean ex){return new Literal(r,name,b,cs,self,ms,t,anon,ex);}
    R self(RC r){return new R(r,new C(name,vars(b)));}
    Literal rc(RC r){return new Literal(r,name,b,cs,self,ms,anon);}
  }
  public record M(S s,List<String>v,E e){
    M(S s){this(s,Collections.nCopies(s.types.size(),"_"),null);}
    M signature(S s){return new M(s,v,e);}
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
    int at(String x){return range(fs.size()).filter(i->fs.get(i).vars.containsKey(x)).findFirst().orElse(-1);}
    T get(String x){var i=at(x);return i==-1?null:fs.get(i).vars.get(x);}
    T adapted(String x){var i=at(x);var t=get(x);
      for(var s=i+1;s<fs.size();s+=1)t=adapt(t,fs.get(s).r,fs.get(s).b);return t;
    }
    boolean escapes(String x){
      var fxs=get(x).ftv().toList();return IntStream.range(at(x)+1,fs.size()).anyMatch(s->!B.v(fs.get(s).b).containsAll(fxs));
    }
    static T adapt(T t,RC r,List<B>b){if(t.und())return t;var caps=TS.kinds(b,t);
      if(r==imm||ii.containsAll(caps))return t.rc(imm);if(r==read){
        if(t.erc()==mut||t.erc()==read)return t.rc(read);
        if(t instanceof X||t instanceof RI)return t.ri();
      }return caps(imm,mut,read).containsAll(caps)?t:t.ri();
    }
    void declare(String x,T t){if(!x.equals("_"))fs.getLast().vars.put(x,t);}
    Object snap(){var m=new HashMap<String,T>();fs.forEach(f->m.putAll(f.vars));return list(m,map(fs,f->f.r),map(fs,f->f.b));}
  }
  static C normC(C c){no(!all(c.types,T::tv)||c.depth()>100);return fillC(c);}
  static T norm(T t){no(!t.tv()||t.depth()>100);return fill(t);}
  static C fillC(C c){return new C(c.name,map(c.types,Frontend::fill));}
  static T fill(T t){return t instanceof R(var r,var c)?new R(or(r,imm),fillC(c)):t;}
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
    case Type(var t,_)->t.ftv();
  };}
  static Stream<String>supFree(List<C>cs){return cs.stream().flatMap(c->typeFree(c.types));}
  static Stream<String>methodFree(IG g,List<M>ms){return ms.stream().flatMap(m->{
    var domBs=B.v(or(m.s.b,list()));
    return cat(typeFree(m.s.types),m.s.t.ftv(),Stream.ofNullable(m.e).flatMap(ei->free(g,ei))).filter(x->!domBs.contains(x));
  });}
  static E copy(Fresh fresh,E e){return switch(e){
    case E.X(var name,var t)->new E.X(name,t);
    case Type(var type,var t)->new Type(type,t);
    case Call c->new Call(copy(fresh,c.e),c.name,c.r,c.y,map(c.es,x->copy(fresh,x)),c.t,c.written);
    case Literal l->{no(!l.anon);var name1=fresh.type(l.name,l.name.arity);
      yield new Literal(l.r,name1,l.b,l.cs,l.self,map(l.ms,m->copy(fresh,m,l.name,name1)),l.t,true,l.expanded);
    }
  };}
  static M copy(Fresh fresh,M m,N name0,N name1){
    var s=Objects.equals(m.s.o,name0)?m.s.o(name1):m.s;
    return new M(s,m.v,m.e==null?null:copy(fresh,m.e));
  }
  static List<Literal>lower(Methods meths){var v=new Visitor(meths);
    for(var di:meths.p.decs){v.owner=v.f(di.name);v.declaration(v.owner,mut,di);}return v.decs;
  }
  record XE(String x,P e){}
  static final class Visitor{
    final Methods meths;N owner;final Vector<String>implicits=new Vector<>();final Vector<Literal>decs=new Vector<>();
    Visitor(Methods meths){this.meths=meths;}
    N f(N tn){
      var p=meths.p;var pN=tn.pk();if(pN.isEmpty()&&primitive(tn.s))return tn.qualify("base");
      var full=new N(pN.isEmpty()?p.map.getOrDefault(tn.s,p.name+"."+tn.s):p.map.getOrDefault(pN,pN)+"."+tn.simple(),tn.arity);
      no(!(full.pk().equals(p.name)?p.names.contains(new N(full.simple(),full.arity)):meths.other.containsKey(full)));return full;
    }
    T type(T t){return t instanceof R(var r,var c)?new R(r,constructor(c)):t;}
    E expr(P e){return switch(e){
      case P.X x->new E.X(x.name);case P.Implicit _->new E.X(implicits.getLast());
      case P.Typed t->t.l==null?new Type(new R(t.r,constructor(t.c))):literal(t.r,list(constructor(t.c)),t.l);
      case P.Declared c->{var name=f(c.dec.name);meths.fresh.owners.put(name,meths.fresh.owners.get(owner));
        yield declaration(name,or(c.r,imm),c.dec);
      }
      case P.Lit l->literal(null,list(),l);
      case P.Call c0->{
        var c=c0.pat!=null?desugar(c0):c0;var recv=expr(c.e);var es=map(c.es,this::expr);
        var sq=or(c.y,new P.Args(null,list()));
        yield new Call(recv,new MN(c.name,c.es.size()),sq.r,map(sq.types,this::type),es,c.y!=null);
      }
    };}
    C constructor(C c){var s=c.name.s;
      var bad=primitive(s)&&(matches(s,UI)&&bits(s)>64||matches(s,SI)&&bits(s)>63||matches(s,SF,UF)&&!floatOk(s));
      no(bad);var res=new C(f(c.name),map(c.types,this::type));no(res.depth()>100);return res;
    }
    String parameter(Par p,boolean patterns){return switch(p.xp){
      case null->"_";case Pat.Name(var x)->patterns&&!x.equals("_")?meths.fresh.variable(owner,x):x;
      case Pat.Des _->meths.fresh.variable(owner,"div");
    };}
    List<M>methods(List<PM>ms){return seq(ms.size(),i->method(ms.get(i),i));}
    S signature(PM mm,int idx){var s=mm.s;var types=map(s.ps,p->type(p.t));if(mm.implicit)types=push(types,u);
      return new S(s.r,s.m==null?null:new MN(s.m,mm.arity()),s.b,types,type(s.t),null,mm.body==null,idx);
    }
    M method(PM m,int idx){var s=signature(m,idx);
      if(m.body==null)return new M(s);var body=m.body;var original=m.s.ps;
      var patterns=any(original,p->p.xp instanceof Pat.Des);
      var ps=map(original,p->parameter(p,patterns));
      var xpats=flat(zip(ps,original,(x,p)->xpat(p.xp,x)),y->y);if(m.implicit){
        var p=meths.fresh.variable(owner,"impl");var inner=patterns?meths.fresh.variable(owner,"impl"):p;ps=push(ps,p);
        if(patterns)xpats=push(xpats,new XE(inner,new P.X(p)));implicits.add(inner);
      }if(patterns){
        var pps=map(xpats,xe->new Par(new Pat.Name(xe.x),u));
        var fl=new P.Lit("_",list(new PM(new PS(null,null,null,pps,u),body,false)));
        body=new P.Call(new P.Typed(imm,new C(new N("base.Destruct",0),list()),null),"#",null,null,push(map(xpats,XE::e),fl));
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
      return new Literal(r,meths.fresh.type(owner,0),list(),impl,l.self,ms,true);
    }
    Literal declaration(N name,RC r,Declaration d){var b=d.b;var cs=map(d.cs,this::constructor);
      no(Core.distinct(b,cs).size()<cs.size());
      var l=new Literal(r,name,b,cs,d.l.self,methods(d.l.ms),false);decs.add(l);return l;
    }
    P.Call desugar(P.Call c){
      var fresh=new P.X(meths.fresh.variable(owner,"eqS"));var res=receiver(c.es.get(1),fresh);
      var s=new PS(null,null,null,list(new Par(c.pat,u),new Par(new Pat.Name(fresh.name),u)),u);
      var par2=new P.Lit("_",list(new PM(s,res,false)));
      return new P.Call(c.e,c.name,c.y,null,list(c.es.get(0),par2));
    }
    P receiver(P par,P atom){
      if(!(par instanceof P.Call c))return atom;return new P.Call(receiver(c.e,atom),c.name,c.y,c.pat,c.es);
    }
  }
  static final class Methods{
    final Pkg p;final Map<N,Literal>other;final Fresh fresh;final HashMap<N,Literal>cache=new HashMap<>();
    final HashMap<E,Object>memo=new HashMap<>();
    Methods(Pkg p,Map<N,Literal>other){this.p=p;this.other=other;fresh=new Fresh(p);}
    List<Literal>headers(List<Literal>decs){var rem=new LinkedHashMap<N,Literal>();
      decs.forEach(d->rem.put(d.name,d));var acc=new Vector<Literal>();while(rem.size()>0){
        var layer=filter(rem.values(),d->!any(d.cs,c->c.name.pk().equals(p.name)&&rem.containsKey(c.name)));
        no(layer.size()==0);for(var d:layer){
          rem.remove(d.name);register(expand(d,false));if(d.self.equals("this"))acc.add(cache.get(d.name));
        }
      }return acc;
    }
    List<C>parents(C c){var d=from(c.name);if(d==null)return list();
      return d.cs.stream().map(ci->new C(ci.name,rename(ci.types,B.v(d.b),c.types))).distinct().toList();
    }
    S alpha(M m,Literal d,C c,Literal child,List<String>scope){var s=m.s;var xs=new Vector<>(B.v(d.b));
      var ts=new Vector<>(c.types);var bs=new Vector<B>();for(var b:s.b){var x=b.x;
        if(fresh.available(child.name,x,scope)){bs.add(b);continue;}xs.add(x);
        var next=new X(fresh.generic(child.name,x,push(B.v(s.b),scope)));ts.add(next);bs.add(new B(next.name,b.caps));
      }return s.subst(bs,xs,ts);
    }
    Literal from(N name){return Frontend.from(name,cache::get,other);}
    Literal expand(Literal d,boolean expanded){
      var implied=flat(d.cs,c->parents(c).stream());
      var supers=Core.distinct(d.b,push(d.cs,implied.stream().sorted(Comparator.comparing(Print::of)).toList()));
      var signatures=flat(filter(d.cs,c->!implied.contains(c)),c->map(from(c.name).ms,m->alpha(m,from(c.name),c,d,list())).stream());
      var res=d.header(supers,pair(names(d.ms,new Vector<>(signatures)),new Vector<>(signatures),d),expanded);
      magic(res,supers);return res;
    }
    Literal implement(Literal d,C c,List<B>scope){var dd=from(c.name);
      List<S>signatures=dd==null?list():map(dd.ms,m->alpha(m,dd,c,d,B.v(scope)));
      return d.header(push(c,parents(c)),pair(names(d.ms,new Vector<>(signatures)),new Vector<>(signatures),d),true);
    }
    void magic(Literal d,List<C>supers){no(supers.stream().filter(c->c.name.equals(widen)).count()>1);
      if(any(supers,c->c.name.equals(identity))){var ms=d.ms;
        no(ms.size()!=1||!ms.get(0).s.m.equals(new MN("#",1)));var s=ms.get(0).s;
        no(!(ms.get(0).e!=null||s.abs||has(from(s.o).cs,identity)));
      }
      if(!any(supers,c->c.name.equals(sealed)))return;
      no(any(supers,c->!c.name.pk().equals(d.name.pk())&&has(from(c.name).cs,sealed)));
    }
    void register(Literal d){
      var ms=map(d.ms,m->m.signature(Core.merge(m.s,m.s)));
      cache.put(d.name,new Literal(or(d.r,imm),d.name,d.b,map(d.cs,Frontend::normC),d.self,ms,d.anon));
    }
    List<M>names(List<M>ms,Vector<S>ss){ss.removeIf(s->any(ms,m->Objects.equals(m.s.m,s.m)));
      var named=filter(ms,m->m.s.m!=null);return push(named,ms.stream().filter(m->m.s.m==null).map(m->name(m,ss)).toList());
    }
    M name(M m,Vector<S>ss){
      var arity=m.s.types.size();for(var abs:list(true,false)){
        var match=filter(ss,s->s.m.arity==arity&&(s.abs||!abs));ss.removeAll(match);
        var count=match.stream().map(s->s.m).distinct().count();no(count>1);if(count==1){var s=m.s;
          return m.signature(new S(s.r,match.get(0).m,s.b,s.types,s.t,s.o,s.abs,s.idx));
        }
      }throw new Fail();
    }
    List<M>pair(List<M>ms,Vector<S>ss,Literal o){var res=new Vector<M>();for(var m:ms){
      var name=m.s.m;var r=m.s.r;
      var taken=filter(ss,s->s.m.equals(name)&&(r==null||r==s.r));ss.removeAll(taken);
      var match=group(taken,s->s.r);
      if(r==null&&match.size()>1&&noH(or(o.r,or(o.t.erc(),imm))).ro()){
        var dead=match.remove(mut);if(dead!=null)ss.addAll(dead);
      }var first=true;
      for(var matches:match.size()==0?list(List.<S>of()):match.values()){
        var mi=first?m:copy(fresh,m,o.name,o.name);first=false;res.add(pair(matches,mi,o));
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
      var b=or(s.b,ss.get(0).b);var rcss=ss.stream().map(e->map(e.b,B::caps)).distinct().toList();
      no(rcss.size()!=1||!rcss.get(0).equals(map(b,B::caps)));
      var aligned=align(ss,b);var first=aligned.get(0);
      var types=seq(s.types.size(),i->s.types.get(i)==u?agreement(o,aligned,e->e.types.get(i)):s.types.get(i));
      var res=s.t==u?agreement(o,aligned,S::t):s.t;
      var impl=om!=null?List.<N>of():aligned.stream().filter(e->!e.abs&&!overridden(e,o)).map(e->e.o).distinct().toList();no(impl.size()>1);
      var out=new S(or(s.r,first.r),first.m,b,types,res,impl.size()==1?impl.get(0):o.name,om==null?impl.size()==0:om.e==null,s.idx);
      return om==null?new M(out):om.signature(out);
    }
    boolean overridden(S s,Literal lit){var sup=s.o;return lit.cs.stream()
      .flatMap(c->cat(Stream.of(c.name),from(c.name).cs.stream().map(C::name))).anyMatch(t->{var d=from(t);
        return!t.equals(sup)&&has(d.cs,sup)&&d.ms.stream().map(M::s).anyMatch(o->o.o.equals(d.name)&&o.m.equals(s.m)&&o.r==s.r);
      });
    }
    T agreement(Literal lit,List<S>ss,Function<S,T>f){var res=ss.stream().map(f).distinct().toList();
      var b=push(lit.b,ss.get(0).b);var first=fill(res.get(0));
      no(!all(res,t->TS.equivalent(b,first,fill(t))));return res.get(0);
    }
    List<S>align(List<S>ss,List<B>b){return map(ss,s->s.subst(b,B.v(s.b),vars(b)));}
    List<Literal>steps(List<Literal>tops){return map(tops,di->di.header(di.cs,map(di.ms,m->body(di,m)),false));}
    M body(Literal di,M m){
      if(m.e==null)return m;var ei=meet(m.e,m.s.t);var g=new IG();
      for(int i=0;i<m.v.size();i++)g.declare(m.v.get(i),m.s.types.get(i));
      g.declare(di.self,di.self(m.s.r));var b=push(di.b,m.s.b);
      ei=solve(b,g,ei);return new M(m.s,m.v,new Core(b,this).core(ei,m.e));
    }
    E meet(E e,T t){
      if(e instanceof Type tt)return type(tt);if(e instanceof Literal l&&l.t.tv())return e;e=ascribe(e,t,null);
      return e.t(meet(e.t(),t));
    }
    T between(R p,R q){var s=below(p,q);if(s!=null)return pick(s,q);s=below(q,p);return s==null?p:pick(s,p);}
    static T pick(T s,R q){return s.tv()||!q.tv()?s:q;}
    T below(R sub,R sup){
      var d=from(sub.c.name);if(d==null)return null;var ps=filter(d.cs,c->c.name.equals(sup.c.name));if(ps.size()==0)return null;
      var refined=meet(map(ps,c->refine(B.v(d.b),new R(null,c),sup)));return sub.with(meet(sub.r,sup.r),meet(sub.c.types,refined));
    }
    T meet(T a,T z){
      if(z.und())return a==u?z:a;if(a.und()||a.equals(z))return z;
      if(a instanceof RI(var p)&&p.equals(z))return a;if(z instanceof RI(var q)&&q.equals(a))return z;
      if(a instanceof R p&&z instanceof R q){if(!p.c.name.equals(q.c.name))return between(p,q);
        return p.with(meet(p.r,q.r),meet(p.c.types,q.c.types));
      }
      if(!(a instanceof RX p&&z instanceof RX(var rc2,var q))||!p.x.equals(q))return a;
      return p.rc(meet(p.r,rc2));
    }
    static RC meet(RC a,RC b){
      if(a==null||b==null)return or(a,b);var x=noH(a);var y=noH(b);
      if(x==y||y==iso||y==read&&x!=iso)return x;if(x==iso||x==read)return y;return imm;
    }
    static RC noH(RC a){return a==readH?read:a==mutH?mut:a;}
    T join(T a,T z){
      if(z==u)return a;if(a==u||a.equals(z))return z;
      var cands=push(candidates(a),candidates(z));for(var top:cands){var res=above(top,cands);if(res!=null)return res;}
      var common=common(cands);return common==null?new Amb(cands):above(common,cands);
    }
    T common(List<T>cands){
      if(!all(cands,c->c instanceof R))return null;
      var heads=cands.stream().map(c->new Vector<>(ancestors((R)c))).reduce((a,b)->{a.retainAll(b);return a;}).get();
      var minimal=filter(heads,h->!any(heads,h2->!h2.equals(h)&&isSuper(h,h2)));
      return minimal.size()==1?sups((R)cands.get(0),minimal.get(0)).get(0):null;
    }
    List<N>ancestors(R t){var d=from(t.c.name);return d==null?list():map(d.cs,C::name);}
    static List<T>candidates(T t){return t instanceof Amb(var cs)?cs:list(t);}
    T above(T top,List<T>cands){
      T res=top;for(var c:cands){var up=lift(c,top);if(up==null)return null;res=shape(res,up);}return res;
    }
    T lift(T c,T top){
      if(c instanceof R r&&top instanceof R rt){if(r.c.name.equals(rt.c.name))return c;
        var up=sups(r,rt.c.name);return up.size()==0?null:up.get(0);
      }return variable(c)!=null&&variable(c).equals(variable(top))?c:null;
    }
    T shape(T a,T b){
      if(a instanceof R p&&b instanceof R q)return p.with(join(p.r,q.r),meet(p.c.types,q.c.types));
      if(a instanceof RX p&&b instanceof RX q)return p.rc(join(p.r,q.r));return meet(a,b);
    }
    static RC join(RC a,RC b){
      if(a==null||b==null)return or(a,b);var x=noH(a);var y=noH(b);return x==y||y==iso?x:x==iso?y:read;
    }
    List<T>join(List<List<T>>tss){return tss.stream().reduce((a,b)->zip(a,b,this::join)).get();}
    List<T>meet(List<T>a,List<T>z){return zip(a,z,this::meet);}
    List<T>meet(List<List<T>>tss){return tss.stream().reduce(this::meet).get();}
    E solve(List<B>b,IG g,E e){
      if(g.snap().equals(memo.get(e)))return e;var grew=0;while(true){var s=g.snap();var oe=next(b,g,e);
        if(oe.equals(e)&&s.equals(g.snap())){memo.put(e,s);return e;}
        grew=oe.t().depth()>e.t().depth()?grew+1:0;no(grew==50);e=oe;
      }
    }
    List<E>solve(List<B>b,IG g,List<E>es){return map(es,ei->solve(b,g,ei));}
    List<E>expect(List<E>es,MS m,List<T>y){return zip(es,m.ps,(e,p)->meet(e,m.inst(p,y)));}
    E next(List<B>b,IG g,E e){return switch(e){
      case E.X x->{
        no(g.escapes(x.name));var a=g.adapted(x.name);var z=x.t;if(a.equals(z))yield x;if(!z.und())updateG(g,x.name,z);
        yield x.t(meet(a,z));
      }
      case Literal l->literal(b,g,l);
      case Call c when c.written||c.r!=null->call(b,g,c);
      case Call c->{
        var ee=solve(b,g,c.e);var es=solve(b,g,c.es);
        var m=ee.t() instanceof R w?signature(w,c.name,null,c.t.erc()):null;if(m==null)yield c.children(ee,es);
        var types=qs(m.mb.size());
        yield new Call(ee,c.name,m.r,types,expect(es,m,types),false).t(meet(c.t,m.inst(m.ret,types)));
      }
      case Type c->type(c);
    };}
    T preferred(R type){var d=from(type.c.name);
      var c=find(d.cs,ci->ci.name.equals(widen));if(c==null)return type;
      var wid=rename(c.types.get(0),B.v(d.b),type.c.types);if(!(wid instanceof R(_,var widC)))return type;
      return new R(type.r,widC);
    }
    M lookup(R w,MN name,RC favorite,RC hint){
      var d=from(w.c.name);if(d==null)return null;var ms=filter(d.ms,m->m.s.m.equals(name));
      Function<RC,M>one=r->find(ms,m->m.s.r==r);
      var r=noH(or(w.r==iso?hint:w.r,imm));
      var order=r==read?list(read,imm,mut):r==mut?list(mut,read,imm):list(imm,read,mut);
      return favorite!=null?one.apply(favorite):ms.size()==1?ms.get(0):order.stream().map(one).filter(Objects::nonNull).findFirst().orElse(null);
    }
    MS signature(R w,MN name,RC favorite,RC hint){var d=from(w.c.name);var m=lookup(w,name,favorite,hint);
      return m==null?null:new MS(m.s.r,push(B.v(d.b),B.v(m.s.b)),d.b,w.c.types,m.s.b,m.s.types,m.s.t);
    }
    static void updateG(IG g,String x,T z){var a=g.get(x);var t=a.und()?z
      :a instanceof R(var aRc,var aC)&&z instanceof R(var bRc,var bC)&&aC.name.equals(bC.name)?new R(aRc==null?bRc:bRc==null?aRc:lowerCap(aRc,bRc),aC)
      :a instanceof RX y&&z instanceof RX(var bRc,var bX)&&y.x.equals(bX)?y.rc(lowerCap(y.r,bRc)):null;
      if(t!=null)g.fs.get(g.at(x)).vars.put(x,t);
    }
    static RC lowerCap(RC a,RC b){a=noH(a);b=noH(b);return a==b||b==read?a:a==read?b:iso;}
    E type(Type t){return t.t.und()?t.t(preferred(t.type)):t;}
    E call(List<B>b,IG g,Call c){var e=solve(b,g,c.e);
      if(!(e.t() instanceof R w)||signature(w,c.name,c.r,null)==null)return c.children(e,solve(b,g,c.es));
      var m=signature(w,c.name,c.r,null);var n=m.cas.size();
      var all0=infer(c,m,c.es,false);var m0=m.arguments(normalize(b,m.cb,all0.subList(0,n)));
      var es=solve(b,g,expect(c.es,m0,normalize(b,m.mb,all0.subList(n,all0.size()))));
      var all=infer(c,m,es,true);var ts=normalize(b,m.cb,all.subList(0,n));
      var y=normalize(b,m.mb,all.subList(n,all.size()));e=meet(e,w.withTs(ts));var m1=m.arguments(ts);
      return new Call(e,c.name,or(c.r,m1.r),y,expect(es,m1,y),meet(c.t,m1.inst(m1.ret,y)),c.written);
    }
    List<T>arguments(MS m,List<E>es,boolean literals){
      var is=range(es.size()).filter(i->!literals||es.get(i) instanceof Literal).boxed().toList();
      Function<Integer,List<T>>ref=i->refine(m.v,m.ps.get(i),es.get(i).t());
      var lower=map(filter(is,i->!(m.ps.get(i) instanceof R)),ref);var exact=map(filter(is,i->m.ps.get(i) instanceof R),ref);
      return meet(push(join(push(qs(m.v.size()),lower)),exact));
    }
    List<T>infer(Call c,MS m,List<E>es,boolean use){var y=MS.fixTargs(c.y,m.mb.size());
      var args=use?arguments(m,es,false):qs(m.v.size());
      var all=meet(List.of(push(m.cas,y),args,refine(m.v,m.ret,c.t)));
      var written=push(m.cas,c.written?y:qs(m.mb.size()));var hard=arguments(m,es,true);
      return zip(zip(written,hard,Methods::choose),all,Methods::choose);
    }
    static T choose(T a,T b){return decided(a)?a:b;}
    static boolean decided(T t){return t.tv()&&!(t instanceof R(var r,_)&&r==null);}
    R self(Literal l){return l.r==null?null:l.self(l.r);}
    E literal(List<B>b,IG g,Literal l){var sp=self(l);if(!l.expanded){var cs0=l.cs;
      l=l.t(!l.anon?sp:cs0.size()==1?new R(l.r,cs0.get(0)):or(sp,l.t));if(!(l.t instanceof R(_,var c)))return l;
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
      var ms=map(l.ms,mi->!mi.s.o.equals(name)?mi:mi.signature(mi.s.o(name1)));
      var cap=noH(or(l.r,w.r));var target=new R(cap,w.c);
      if(all(l.ms,m->m.e==null)&&from(w.c.name)!=null)return new Type(target,preferred(target));
      var own=w.c.name.equals(l.name);
      var cs=Core.distinct(bs,own?parents(w.c):push(w.c,parents(w.c)));magic(l,cs);
      l=new Literal(cap,name1,bs,cs,l.self,ms,w,l.anon,l.expanded);
      if(own)l=l.t(self(l));register(l);return l;
    }
    record TSM(List<T>types,M m){}
    TSM header(R w,M m){
      var s=m.s;var omh=lookup(w,s.m,s.r,null);if(omh==null)return new TSM(w.c.types,m);
      var v=bound(w,refine(w,s,omh.s));
      return new TSM(erase(v.c.types,B.v(s.b)),m.signature(signature(v,s)));
    }
    TSM method(List<B>b,IG g,Literal l,R sp,R w,M m){var bs=l.anon?b:l.b;
      g.fs.add(new IG.Frame(m.s.r,bs,new HashMap<>()));
      g.declare(l.self,sp==null?u:new R(sp.r==null?null:sp.r.mutable(),sp.c));
      g.fs.add(new IG.Frame(m.s.r,bs,new HashMap<>()));
      for(int i=0;i<m.v.size();i++)g.declare(m.v.get(i),m.s.types.get(i));
      var e=solve(push(bs,m.s.b),g,meet(m.e,m.s.t));
      var args=zip(m.v,m.s.types,(x,t)->x.equals("_")?t:meet(t,g.get(x)));g.fs.removeLast();
      g.fs.removeLast();var h=header(w,m.signature(m.s.types(args,meet(m.s.t,e.t()))));var s=h.m.s;
      return new TSM(h.types,new M(s,m.v,meet(e,s.t)));
    }
    List<T>refine(R w,S sig,S imh){var Xs=B.v(from(w.c.name).b);
      var byArg=zip(imh.types,sig.types,(t,it)->refine(Xs,t,it));var body=meet(push(byArg,refine(Xs,imh.t,sig.t)));
      return zip(w.c.types,body,this::keep);
    }
    T keep(T decided,T body){
      var isolated=decided instanceof RX(var aRc,_)&&aRc==iso;
      if(variable(decided)!=null&&variable(decided).equals(variable(body))&&!isolated)return decided;
      if(!(decided instanceof R(var aRc,var aC)&&body instanceof R b))return meet(decided,body);
      if(!aC.name.equals(b.c.name)){var supers=sups(b,aC.name);
        return supers.size()==0?decided:keep(decided,supers.get(0));
      }
      return b.with(or(aRc,b.r),zip(aC.types,b.c.types,this::keep));
    }
    S signature(R w,S sig){
      var h=signature(w,sig.m,sig.r,null);var v=vars(sig.b);
      return sig.types(map(h.ps,p->h.inst(p,v)),h.inst(h.ret,v));
    }
    List<T>erase(List<T>types,List<String>mb){
      if(mb.size()==0)return types;
      return map(types,t->t instanceof R w?bound(w,erase(w.c.types,mb)):mb.contains(variable(t))?u:t);
    }
    List<T>refine(List<String>v,T t,T a){
      if(a.und())return qs(v.size());return switch(t){
        case X x->{var n=v.indexOf(x.name);yield seq(v.size(),i->i==n?a:u);}
        case RX(_,var x)->refine(v,x,switch(a){
          case RX(_,var p)->p;case RI(var p)->p;case R(_,var c)->new R(null,c);default->a;
        });
        case RI(var x)->refine(v,x,a instanceof RI(var p)?p:a);case R w->propagate(v,w,a);
        case U _,Amb _->qs(v.size());
      };
    }
    boolean isSuper(N a,N b){var d=from(b);return d!=null&&has(d.cs,a);}
    List<R>sups(R src,N target){var d=from(src.c.name);if(d==null)return list();
      return d.cs.stream().filter(sc->sc.name.equals(target)).distinct()
        .map(ci->(R)rename(new R(src.r,ci),B.v(d.b),src.c.types)).toList();
    }
    List<T>propagate(List<String>v,R r,T a){
      if(!(a instanceof R cc))return qs(v.size());var c=r.c;if(!cc.c.name.equals(c.name)){var supOk=sups(cc,c.name);
        if(supOk.size()>0)return propagate(v,r,supOk.get(0));var subOk=sups(r,cc.c.name);
        if(subOk.size()>0)return propagate(v,subOk.get(0),a);return qs(v.size());
      }
      var res=zip(c.types,cc.c.types,(t,ti)->t instanceof R rr&&!(ti instanceof R ci&&ci.c.name.equals(rr.c.name))?qs(v.size()):refine(v,t,ti));
      return res.size()==0?qs(v.size()):meet(res);
    }
    E ascribe(E arg,T expected,MN called){
      if(!(expected instanceof R exp))return arg;
      return switch(arg){
        case Call c->c.children(ascribe(c.e,expected,c.name),c.es);
        case Literal l when l.expanded||!l.anon||l.cs.size()>0||!l.t.und()->arg;
        case Literal l when called==null||implementable(exp.c.name)&&!declares(l,called)->l.t(new R(exp.r,new C(exp.c.name,qs(exp.c.types.size()))));
        case Literal l->{var res=new Literal(imm,l.name,l.b,l.cs,l.self,l.ms,true);yield res.t(self(res));}
        default->arg;
      };
    }
    boolean declares(Literal l,MN called){return any(l.ms,m->called.equals(m.s.m)&&m.s.t!=u&&!any(m.s.types,t->t==u));}
    boolean implementable(N head){
      var d=from(head);if(d==null)return false;var foreign=!head.pk().equals(p.name)&&(!head.visible()||has(d.cs,sealed));
      return!foreign&&TS.inst(d);
    }
    static T normalize(T t,Set<RC>al){
      if(al.size()==1)return t.rc(al.iterator().next());if(!(t instanceof R(var r,var c)))return t;
      if(!(r==null||r==iso&&!al.contains(iso)))return t;return new R(al.contains(imm)?null:read,c);
    }
    static List<T>normalize(List<B>scope,List<B>b,List<T>types){
      return zip(types,b,(ti,bi)->variable(ti)==null||B.get(scope,variable(ti)).caps.equals(bi.caps)?normalize(ti,bi.caps):ti);
    }
    R bound(R w,List<T>types){
      var d=from(w.c.name);return d==null?w.withTs(types):w.withTs(zip(types,d.b,(ti,bi)->normalize(ti,bi.caps)));
    }
  }
  record Core(List<B>ctx,Methods meths){
    E core(E exp,E orig){return switch(exp){
      case E.X(var name,_)->new E.X(name);
      case Type(var type,_)->new Type((R)norm(type));
      case Literal le->literal(le,(Literal)orig);
      case Call e->{var o=(Call)orig;var types=o.y.size()==0?e.y:o.y;
        yield new Call(core(e.e,o.e),e.name,or(e.r,imm),seq(types.size(),i->targ(e,types.get(i),i)),zip(e.es,o.es,this::core),false);
      }
    };}
    T targ(Call e,T t,int i){
      if(t!=u)return norm(fillVoid(t));
      var m=e.e.t() instanceof R w?meths.lookup(w,e.name,e.r,null):null;var caps=m==null?caps(imm):m.s.b.get(i).caps;
      return voidT(caps.contains(imm)?imm:caps.iterator().next());
    }
    static T voidT(RC r){return new R(r,new C(voidName,list()));}
    static T fillVoid(T t){no(t instanceof Amb);return t==u?voidT(imm):t instanceof R w?w.withTs(map(w.c.types,Core::fillVoid)):t;}
    Literal literal(Literal e,Literal o){
      no(!(e.t instanceof R)&&!e.t.und());var b=e.b;if(e.anon&&b.size()==0){var g=new IG();
        b=cat(supFree(e.cs),methodFree(g,e.ms),methodFree(g,o.ms)).distinct().map(x->B.get(ctx,x)).toList();
      }var name=e.name.arity(b.size());
      var inner=e.anon?with(b):new Core(b,meths);
      var ms=e.ms.stream().map(me->inner.m(me,me.e==null?me:o.ms.get(me.s.idx)))
        .map(m->!m.s.o.equals(e.name)?m:m.signature(m.s.o(name))).toList();
      var cs=map(distinct(inner.ctx,push(o.cs,e.cs)),Frontend::normC);
      return new Literal(or(e.r,imm),name,b,cs,e.self,ms,e.anon);
    }
    static List<C>distinct(List<B>b,List<C>cs){var res=new Vector<C>();
      for(var c:cs){if(!any(res,r->TS.equivalent(b,fill(new R(imm,r)),fill(new R(imm,c)))))res.add(c);}return res;
    }
    Core with(List<B>b){return new Core(push(ctx,b).stream().distinct().toList(),meths);}
    M m(M e,M o){var s=merge(e.s,o.s);return new M(s,e.v,e.e==null?null:with(s.b).core(e.e,o.e));}
    static S merge(S inf,S usr){var types=zip(usr.types,inf.types,(y,i)->y==u?i:y);
      return new S(or(usr.r,or(inf.r,imm)),required(or(usr.m,inf.m)),or(usr.b,or(inf.b,list())),
        map(types,Frontend::norm),norm(usr.t==u?inf.t:usr.t),required(or(usr.o,inf.o)),usr.abs,usr.idx);
    }
  }
  record G(G tail,String name,T t){
    static final G empty=new G(null,null,null);
    G add(String name,T t){return new G(this,name,t);}
    G map(UnaryOperator<T>f){return this==empty?this:new G(tail.map(f),name,t==null?null:f.apply(t));}
    T bind(String x){return this==empty?null:name.equals(x)?t:tail.bind(x);}
    G filter(Literal l,boolean cf){
      if(this==empty)return this;var rest=tail.filter(l,cf);
      var drop=cf||t!=null&&!t.ftv().allMatch(B.v(l.b)::contains);return new G(rest,name,drop?null:t);
    }
  }
  record MT(RC r,List<T>types,T t){}
  enum Mode{
    reading(iso,readH,mutH,readH),flexy(iso,imm,mutH,readH),hyg(mutH,readH,mutH,readH),strong(iso,imm,iso,imm);
    final RC m,r,mh,rh;
    Mode(RC m,RC r,RC mh,RC rh){this.m=m;this.r=r;this.mh=mh;this.rh=rh;}
    RC of(RC x){return switch(x){case mut->m;case read->r;case mutH->mh;case readH->rh;default->x;};}
  }
  record TS(Function<N,Literal>decs){
    static void check(List<Literal>tops,Map<N,Literal>other){var map=new HashMap<N,Literal>();
      tops.forEach(t->collect(t,map));var sys=new TS(n->from(n,map::get,other));tops.forEach(l->sys.check(G.empty,l,has(l.cs,cf)?imm:l.r));
    }
    static void collect(E e,HashMap<N,Literal>map){if(e instanceof Literal l)map.put(l.name,l);e.children().forEach(c->collect(c,map));}
    boolean kinded(List<B>b,T t,Set<RC>al){
      if(!al.containsAll(kinds(b,t)))return false;
      if(!(t instanceof R(_,var c)))return true;var params=decs.apply(c.name).b;
      return all(zip(c.types,params,(ti,p)->kinded(b,ti,p.caps)),v->v);
    }
    void kind(List<B>b,T t,Set<RC>al){no(!kinded(b,t,al));}
    static Set<RC>kinds(List<B>b,T t){return switch(t){
      case R(var r,_)->caps(r);case RX(var r,_)->caps(r);case X(var x)->B.get(b,x).caps;case U _,Amb _->throw new Fail();
      case RI(var x)->{var caps=kinds(b,x);
        yield ii.containsAll(caps)?caps(imm):caps(mut,mutH,read,readH).containsAll(caps)?caps(read):caps(read,imm);
      }
    };}
    G adapt(G g,Literal l,M m){return g.map(t->IG.adapt(t,m.s.r,l.b));}
    G discard(G g,Literal l){return g.map(t->{
      var drop=!kinded(l.b,t,plain)||l.r.ii()&&!kinded(l.b,t,ii);return drop?null:t;
    });}
    boolean sub(List<B>b,T a,T z){return a.equals(z)
      ||z instanceof RI(var q)&&a instanceof X x&&q.name.equals(x.name)&&kinded(b,x,plain)
      ||shape(b,a,z)
      ||a instanceof R(var rc1,var c1)&&any(decs.apply(c1.name).cs,ci->sub(b,rename(new R(rc1,ci),B.v(decs.apply(c1.name).b),c1.types),z));
    }
    List<T>type(List<B>b,G g,E e,List<T>rs){return switch(e){
      case E.X x->{var t=g.bind(x.name);no(t==null);yield reqs(b,t,rs,false);}
      case Type t->{
        kind(b,t.type,allRC);var ll=decs.apply(t.type.c.name);no(!inst(ll));var r=t.type.r;
        var getIso=(r.ro()&&!mutable(ll))||r==mut||r==mutH;var l=ll.rc(getIso?iso:r);
        l.ms.forEach(m->no(m.s.abs&&callable(l.r,m.s.r)));yield reqs(b,getIso?t.type.rc(iso):t.type,rs,true);
      }
      case Literal l->literal(b,g,l,rs);case Call c->call(b,g,c,rs);
    };}
    static boolean inst(Literal l){return l.self.equals("this")||has(l.cs,cf);}
    static long count(String x,E e,boolean active){
      var here=e instanceof E.X v&&v.name.equals(x)?1:0;
      if(active&&e instanceof Literal)return here;return here+e.children().mapToLong(c->count(x,c,active)).sum();
    }
    static boolean mutable(Literal l){return any(l.ms,m->m.s.abs&&m.s.r==mut);}
    List<T>reqs(List<B>b,T got,List<T>rs,boolean concrete){
      if(rs.size()==0)return list(got);no(concrete&&any(rs,r->!(r instanceof R)));return map(rs,r->sub(b,got,r)?got:null);
    }
    List<T>literal(List<B>bs1,G g,Literal _l,List<T>rs){
      var named=!_l.self.equals("_");var free=has(_l.cs,cf);
      var getIso=((_l.r.ro()&&!mutable(_l))||_l.r==mut)&&cf(_l.b,g.filter(_l,free),_l);
      var l=getIso?_l.rc(iso):_l;
      no(any(rs,r->!(r instanceof R)));
      var t=l.self(l.r);kind(bs1,t,allRC);check(discard(g.filter(l,free),l),l,_l.r.mutable());
      no(named&&count(_l.self,_l,false)==0);no(any(l.ms,m->m.e!=null&&!inst(l)&&!callable(l.r,m.s.r)));
      l.ms.forEach(m->no(m.s.abs&&callable(l.r,m.s.r)));return reqs(bs1,t,rs,false);
    }
    static boolean cf(List<B>b,G g,E e){
      if(!(e instanceof E.X x))return e.children().allMatch(c->cf(b,g,c));
      return g.bind(x.name)==null||all(kinds(b,g.bind(x.name)),RC::ii);
    }
    static boolean callable(RC litRC,RC recRc){return recRc!=mut||!litRC.ro();}
    void check(G g,Literal l,RC self){
      if(has(l.cs,identity)){var m=l.ms.get(0);var isId=switch(m.e){
        case null->true;
        case E.X(var name,_)->name.equals(m.v.get(0));
        case Call c->c.e instanceof E.X(var recv,_)&&recv.equals(m.v.get(0))&&c.name.equals(new MN(".as",1))
          &&m.s.types.get(0) instanceof R(_,var cc)&&has(decs.apply(cc.name).cs,container);
        default->false;
      };no(!isId);}
      var delta=l.b;for(var c:l.cs){kind(delta,new R(imm,c),allRC);no(!inst(decs.apply(c.name)));}var sources=new Vector<S>();
      for(var parent:l.cs){var sup=decs.apply(parent.name);for(var m:sup.ms){
        if(!m.s.o.equals(sup.name))continue;var s=m.s;var canonical=canonical(l,s.m,s.r).b;
        var xs=B.v(push(s.b,sup.b));var ts=push(vars(canonical),parent.types);
        sources.add(s.subst(canonical,xs,ts));
      }}
      for(var m:l.ms){if(m.s.o.equals(l.name))sources.add(m.s);}
      group(sources,s->new Key(s.r,s.m)).forEach((k,sigs)->{
        var chosen=canonical(l,k.name,k.r);var ctx=push(l.b,chosen.b);for(var s:sigs){
          for(int i=0;i<chosen.types.size();i++)no(!same(ctx,chosen.types.get(i),s.types.get(i))||!sub(ctx,s.types.get(i),chosen.types.get(i)));
          no(!same(ctx,chosen.t,s.t)||!sub(ctx,chosen.t,s.t));
        }
      });
      var g1=g.add(l.self,l.self(self));for(var m:l.ms){var g2=adapt(g1,l,m);
        var bs=push(delta,m.s.b);m.s.types.forEach(t->kind(bs,t,allRC));kind(bs,m.s.t,allRC);if(m.e==null)continue;
        for(int i=0;i<m.v.size();i++)g2=g2.add(m.v.get(i),m.s.types.get(i));no(type(bs,g2,m.e,list(m.s.t)).get(0)==null);
        for(int i=0;i<m.v.size();i++){var x=m.v.get(i);if(kinded(bs,m.s.types.get(i),caps(mut,read,mutH,readH,imm)))continue;
          no(count(x,m.e,true)>0&&count(x,m.e,false)!=1);
        }
      }
    }
    static S canonical(Literal l,MN name,RC r){return find(l.ms,m->m.s.m.equals(name)&&m.s.r==r).s;}
    static boolean shape(List<B>b,T a,T z){
      if(!equivalent(b,a.rc(mut),z.rc(mut)))return false;var rcs2=kinds(b,z);
      return all(kinds(b,a),r1->all(rcs2,r1::sub));
    }
    static boolean same(List<B>b,T p,T q){return(p instanceof RI)==(q instanceof RI)&&p.erc()==q.erc()||equivalent(b,p,q);}
    static boolean equivalent(List<B>b,T p,T q){
      if(p.equals(q))return true;
      if(!(p instanceof R(var aRc,var aC)&&q instanceof R(var bRc,var bC))){
        if(!(p.rc(imm) instanceof RX(_,var x))||!p.rc(imm).equals(q.rc(imm)))return false;
        return B.get(b,x.name).caps.size()==1&&kinds(b,p).equals(kinds(b,q));
      }
      return aRc==bRc&&aC.name.equals(bC.name)&&all(zip(aC.types,bC.types,(x,y)->equivalent(b,x,y)),v->v);
    }
    List<T>call(List<B>b,G g,Call c,List<T>rs){
      if(!(type(b,g,c.e,list()).get(0) instanceof R h))throw new Fail();var d=decs.apply(h.c.name);
      var s=required(find(d.ms,m->m.s.m.equals(c.name)&&m.s.r==c.r)).s;
      no(s.b.size()!=c.y.size());for(int i=0;i<c.y.size();i++)kind(b,c.y.get(i),s.b.get(i).caps);
      var v=B.v(push(d.b,s.b));var ts0=push(h.c.types,c.y);
      var base=new MT(s.r,rename(s.types,v,ts0),rename(s.t,v,ts0));
      var app=filter(promotions(b,base),m->h.r.sub(m.r));no(app.size()==0);
      var possible=app;for(int i=0;i<c.es.size();i++){var ai=i;
        var reqs=app.stream().map(m->m.types.get(ai)).distinct().toList();var got=type(b,g,c.es.get(i),reqs);
        no(all(got,Objects::isNull));possible=filter(possible,m->got.get(reqs.indexOf(m.types.get(ai)))!=null);
      }
      no(possible.size()==0);var candidates=possible;
      if(rs.size()==0)return list(best(b,candidates));return map(rs,req->{
        var ok=filter(candidates,m->sub(b,m.t,req));return ok.size()==0?null:best(b,ok);
      });
    }
    T best(List<B>b,List<MT>ms){var types=map(ms,MT::t);return find(types,p->!any(types,q->!q.equals(p)&&sub(b,q,p)));}
    static RC lub(Set<RC>caps){return bound(caps,RC::sub);}
    static RC glb(Set<RC>caps){return bound(caps,(p,q)->q.sub(p));}
    static RC bound(Set<RC>caps,BiPredicate<RC,RC>le){
      var up=Stream.of(RC.values()).filter(p->all(caps,x->le.test(x,p))).toList();return find(up,p->all(up,o->le.test(p,o)));
    }
    static List<MT>promotions(List<B>d,MT m){
      return cat(Stream.of(m,apply(d,m,flexy,flexy,-1,flexy),apply(d,m,strong,strong,-1,strong),apply(d,m,reading,reading,-1,hyg),apply(d,m,hyg,flexy,-1,hyg)),
        range(m.types.size()).mapToObj(i->apply(d,m,flexy,flexy,i,hyg))).distinct().toList();
    }
    static MT apply(List<B>d,MT m,Mode receiver,Mode args,int at,Mode result){
      return new MT(receiver.of(m.r),seq(m.types.size(),j->adapt(d,m.types.get(j),j==at?hyg:args,TS::glb)),adapt(d,m.t,result,TS::lub));
    }
    static T adapt(List<B>d,T t,Mode mode,Function<Set<RC>,RC>f){return switch(t){
      case R w->w.rc(mode.of(w.r));case RX rcx->rcx.rc(mode.of(rcx.r));
      case X x->variable(d,x,r->r,mode,f,t);case RI(var x)->variable(d,x,RC::ri,mode,f,t);case U _,Amb _->t;
    };}
    static T variable(List<B>d,X x,UnaryOperator<RC>inst,Mode mode,Function<Set<RC>,RC>f,T original){
      var caps=EnumSet.copyOf(map(B.get(d,x.name).caps,inst));if(all(caps,r->mode.of(r)==r))return original;
      return new RX(f.apply(EnumSet.copyOf(map(caps,mode::of))),x);
    }
  }
}
