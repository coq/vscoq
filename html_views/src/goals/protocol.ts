interface ControllerEvent {
  eventName: string;
  params: ResizeEvent // | | | | | ;
}
interface ResizeEvent {
  columns: number;
}

interface GoalUpdate {
  command: 'goal-update',
  goal: CommandResult
}

interface SettingsUpdate extends SettingsState {
  command: 'settings-update'
}

interface SettingsState {
  fontFamily?: string,
  fontSize?: string,
  fontWeight?: string,
  cssFile?: string,
}

type ProofViewProtocol = GoalUpdate | SettingsUpdate;

type TextDifference = "added";

interface TextAnnotation {
  /** the relationship this text has to the text of another state */
  diff?: TextDifference,
  /** what to display instead of this text */
  substitution?: string,
  /** the underlying text, possibly with more annotations */
  text: string
}

interface ScopedText {
  /** A scope identifier */
  scope: string,
  /** the underlying text, possibly with more annotations */
  text: AnnotatedText
}

type AnnotatedText = string | TextAnnotation | ScopedText | (string | TextAnnotation | ScopedText)[];


enum HypothesisDifference { None, Changed, New, MovedUp, MovedDown }

interface Hypothesis {
  identifier: string;
  relation: string;
  expression: AnnotatedText;
  diff: HypothesisDifference;
}
interface Goal {
  id: number;
  hypotheses: Hypothesis[];
  goal: AnnotatedText;
}
interface UnfocusedGoalStack {
  // subgoals that appear before the focus
  before: Goal[];
  // reference to the more-focused background goals
  next?: UnfocusedGoalStack
  // subgoals that appear after the focus
  after: Goal[];
}

interface FailValue {
  message: AnnotatedText;
  location?: Location;
}

interface ProofView {
  goals: Goal[];
  backgroundGoals: UnfocusedGoalStack,
  shelvedGoals: Goal[],
  abandonedGoals: Goal[],
}

interface CommandInterrupted {
  range: any
}

type FocusPosition = {focus: any}
type NotRunningTag = {type: 'not-running'}
type NoProofTag = {type: 'no-proof'}
type FailureTag = {type: 'failure'}
type ProofViewTag = {type: 'proof-view'}
type InterruptedTag = {type: 'interrupted'}
type NotRunningResult = NotRunningTag
type NoProofResult = NoProofTag
type FailureResult = FailValue & FailureTag
type ProofViewResult = ProofView & ProofViewTag
type InterruptedResult = CommandInterrupted & InterruptedTag
type CommandResult =
  NotRunningTag |
  (FailureResult & FocusPosition) |
  (ProofViewResult & FocusPosition) |
  (InterruptedResult & FocusPosition) |
  (NoProofResult & FocusPosition);
