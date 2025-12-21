module FearlessFrontend {
  requires transitive Commons;
  requires org.junit.jupiter.api;
  exports core;
  exports fearlessFullGrammar; //TName, MName
  exports fearlessParser;//RC
  exports message;//only for the testing module
  exports testUtils;//only for the testing module
}