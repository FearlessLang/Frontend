module FearlessFrontend {
  requires transitive Commons;
  requires org.junit.jupiter.api;
  exports core;
  exports testUtils;//only for the testing module
}