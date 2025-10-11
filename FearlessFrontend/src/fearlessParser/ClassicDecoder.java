package fearlessParser;

import utils.Bug;

public final class ClassicDecoder{
 private final String s;
 private final int base; // absolute offset of s in the token, if any
 private final StringInfo.RangeMsg onErr;
 private final StringBuilder out= new StringBuilder();
 private int i= 0;
 private boolean lastCurly= false;
 ClassicDecoder(String s, int base, StringInfo.RangeMsg onErr){
   this.s= s; this.base= base; this.onErr= onErr;
 }
 String of(){
   while (i < s.length()){
     char c = s.charAt(i);
     if (c == '\\'){ handleEscape(); continue; }
     out.append(c); i++;
     lastCurly = c == '{';
   }
   return out.toString();
 }
 private void handleEscape(){
   int from= i;
   i++;
   assert i < s.length();
   char e= s.charAt(i);
   if (e == '\\'){ out.append('\\'); i++; return; }
   if (e == '\"'){ out.append('\"'); i++; return; }
   if (e == 'n'){ out.append('\n'); i++; return; }
   if (e == 't'){ out.append('\t'); i++; return; }
   if (e == 'u' && lastCurly){ handleUnicodeBlock(); return; }
   if (e == 'u'){ throw report(from, 2, "\\u must be used in a \"{..}\" group. (eg. {\\u34\\u35})"); }
   throw Bug.unreachable();
 }
 private void handleUnicodeBlock(){
   lastCurly= false;
   int open= i - 2;
   i++;
   int close= s.indexOf('}', i);
   if (close < 0){ throw report(open, 1, "Unclosed '{' for unicode payload"); }
   //if (close == i){ report(open, 2, "Empty unicode payload"); }
   String payload= s.substring(i - 2, close);
   String decoded= new PayloadParsing(base + i - 2, payload, onErr).of();
   out.deleteCharAt(out.length()-1);
   out.append(decoded);
   i = close + 1;
 }
 private RuntimeException report(int fromRel, int len, String msg){
   throw new PayloadParsing(base + i, "", onErr).report(fromRel, len, msg);
 }
}