The compact frontend is a second implementation of the Fearless frontend, written to be as short as possible.
It has the same observable behavior as the full frontend, except that every error is the single exception Frontend.Fail.
It has no type expression: `A` is the object literal `A{}`, and an object literal without methods is a declaration like any other.
It has no variable _: the lowering gives every parameter _ and every self name _ a fresh name of the form _a0, _b0, ..., while the full frontend keeps _.
The tests compare the two printed cores after FearlessTestBase.canon rewrites both:
every name of the form _a0 becomes _;
a literal with a fresh name, the self name _ and no method body prints as its head type, as a type expression prints;
then the fresh names are renumbered in order of first appearance, restarting at every literal body.
Its source is the three files src/compact/Frontend.java, src/compact/Util.java and src/compact/Print.java.

Testing:
From Coordinator/Build/src, this command runs the Frontend tests on both frontends:
  /opt/jdk-26.0.2/bin/java -ea --module-path ../../../Commons/Commons.jar --add-modules Commons scripts/TestAllFrontend.java compact
With the argument compact, every typeOk test also requires the compact frontend to print the same core as the full frontend,
every typeFail test also requires Frontend.Fail,
and the fuzz test compares the two frontends on every mutated program.
The parse tests check only the full frontend, also with the argument compact.
Without the argument compact, the tests run only the full frontend.
Every test script in Coordinator/Build/src/scripts, except TestAgentTools.java, accepts the argument compact.
The argument compact reaches every JUnit run the script starts.

Measuring the size:
The size of the compact frontend is the number of LLM tokens of its three source files.
Count each of the three files as its own message with the count_tokens endpoint of the Anthropic API, and add up the three counts.
From Frontend/compact_frontend, with Claude Code logged in:
  token=$(jq -r '.claudeAiOauth.accessToken' ~/.claude/.credentials.json)
  for f in Frontend Util Print; do
    jq -n --rawfile c src/compact/$f.java '{model:"claude-opus-5-5",messages:[{role:"user",content:$c}]}' |
    curl -s https://api.anthropic.com/v1/messages/count_tokens -H "Authorization: Bearer $token" -H "anthropic-beta: oauth-2025-04-20" -H "anthropic-version: 2023-06-01" -H "content-type: application/json" -d @- |
    jq .input_tokens
  done | paste -sd+ | bc

Recurrent tasks on this compact frontend:
Compaction:
Look to the full frontend code and the 3 files of the compact frontend and find ways to further compact the compacted frontend while keeping the same observable behavior.

DeltaHunt:
look to Frontend compact and compare with the full version with good errors.
Find a difference,
A: some place where the full version pass and the compact fails.
B: some place where the compact pass and the full fails.
C: some place where they both pass but with different tree printout.

Then, for each of the identified cases, try to see if the case is isolated or if it is part of a more general family.
Open a PR with the tests showing the difference by failing, do not fix the code, just add the failing tests. If there is a family of similar tests, add only a few well chosen representative (could be just one)

A difference counts only in the result of the whole frontend: the printed core, or the fact that the frontend fails.
The compact frontend may detect an error in a different phase than the full frontend.

DeltaWisdom:
After a DeltaHunt: for each difference in the semantic, try to understand what is the wiser semantic.
Do not try to understand what is the intended semantic, or what the user may want. Try to understand what is the semantic that actually makes more sense. Treat the compact and the full frontend as two implementation wrote by different people; who did the right choice, and why? What are the cost of each choice.

OverallWisdom:
Read the whole of the compact frontend, directly with no sub agents. Try to see if the design is wise.
Is this a reasonable design for a language? what kind of pitfall there may be? What 'bad ideas' survived?
What kind of semantic wrinkles are there because this was designed over years instead of all together in a single cohesive shot?
How other languages create trouble for users? Is this design of fearless making the same mistake or new ones?
