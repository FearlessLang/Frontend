The compact frontend is a second implementation of the Fearless frontend, written to be as short as possible.
It has the same observable behavior as the full frontend, except that every error is the single exception Frontend.Fail.
Its source is the three files src/compact/Frontend.java, src/compact/Util.java and src/compact/Print.java.

Testing:
The Frontend tests run the compact frontend only when asked.
From Coordinator/Build/src, this command runs the Frontend tests on both frontends:
  /opt/jdk-26.0.2/bin/java -ea --module-path ../../../Commons/Commons.jar --add-modules Commons scripts/TestAllFrontend.java compact
With the argument compact, every typeOk test also requires the compact frontend to print the same core as the full frontend,
every failing test also requires Frontend.Fail, the parse tests require the same accept or reject outcome,
and the fuzz test compares the two frontends on every mutated program.
Without the argument compact, the tests run only the full frontend.
Every test script in Coordinator/Build/src/scripts, except TestAgentTools.java, accepts the argument compact.
The argument compact reaches every JUnit run the script starts.
For example, TestAllFrontendCoordinatorIntegration.java compact also checks the compact frontend on the Frontend tests.

Measuring the size:
The size of the compact frontend is the number of LLM tokens of its three source files.
The count_tokens endpoint of the Anthropic API counts the tokens of one message.
Count each of the three files as its own message and add up the three counts.
Each count includes a few tokens of message overhead; counting the files one by one keeps the numbers comparable between rounds.
The models claude-opus-5-5, claude-fable-5-1 and claude-sonnet-5-5 give the same counts.
From Frontend/compact_frontend, with Claude Code logged in:
  token=$(jq -r '.claudeAiOauth.accessToken' ~/.claude/.credentials.json)
  for f in Frontend Util Print; do
    jq -n --rawfile c src/compact/$f.java '{model:"claude-opus-5-5",messages:[{role:"user",content:$c}]}' |
    curl -s https://api.anthropic.com/v1/messages/count_tokens -H "Authorization: Bearer $token" -H "anthropic-beta: oauth-2025-04-20" -H "anthropic-version: 2023-06-01" -H "content-type: application/json" -d @- |
    jq .input_tokens
  done | paste -sd+ | bc
With an API key instead, replace the two headers Authorization and anthropic-beta with -H "x-api-key: $ANTHROPIC_API_KEY".

Recurrent tasks on this compact frontend:
Compaction:
Look to the full frontend code and the 3 files of the compact frontend and find ways to further compact the compacted frontend while keeping the same observable behavior, except that errors are all just a single kind.

DeltaHunt:
look to Frontend compact and compare with the full version with good errors.
Find a difference,
A: some place where the full version pass and the compact fails.
B: some place where the compact pass and the full fails.
C: some place where they both pass but with different tree printout.

Then, for each of the identified cases, try to see if the case is isolated or if it is part of a more general famly.
Open a PR with the tests showing the difference by failing, do not fix the code, just add the failing tests. If there is a family of similar tests, add only a few well chosen representative (could be just one)
