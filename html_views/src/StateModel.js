/// <reference path="ui-util.ts" />
'use strict';
(function (HypothesisDifference) {
    HypothesisDifference[HypothesisDifference["Changed"] = 0] = "Changed";
    HypothesisDifference[HypothesisDifference["New"] = 1] = "New";
    HypothesisDifference[HypothesisDifference["Moved"] = 2] = "Moved";
})(exports.HypothesisDifference || (exports.HypothesisDifference = {}));
var HypothesisDifference = exports.HypothesisDifference;
var DisplayState;
(function (DisplayState) {
    DisplayState[DisplayState["Proof"] = 0] = "Proof";
    DisplayState[DisplayState["Top"] = 1] = "Top";
    DisplayState[DisplayState["Error"] = 2] = "Error";
})(DisplayState || (DisplayState = {}));
function getDisplayState(state) {
    if (state.error)
        return DisplayState.Error;
    if (state.goals || state.backgroundGoals || state.abandonedGoals || state.shelvedGoals)
        return DisplayState.Proof;
    else
        return DisplayState.Top;
}
function countAllGoals(state) {
    var result = (state.goals ? state.goals.length : 0)
        + (state.backgroundGoals ? state.backgroundGoals.length : 0)
        + (state.abandonedGoals ? state.abandonedGoals.length : 0)
        + (state.shelvedGoals ? state.shelvedGoals.length : 0);
    return result;
}
function createHypothesis(ident, rel, expr) {
    return makeElement('li', { class: 'hypothesis' }, [makeElement('span', { class: 'ident' }, makeText(ident)),
        makeElement('span', { class: 'rel' }, makeText(rel)),
        makeElement('span', { class: 'expr' }, makeText(expr))
    ]);
}
function createHypotheses(hyps) {
    return makeElement('ul', { class: "hypotheses" }, hyps.map(function (hyp) {
        return createHypothesis(hyp.identifier, hyp.relation, hyp.expression);
    }));
}
function createGoal(goal, idx, count) {
    return makeElement('li', { class: "goal" }, [makeElement('span', { class: 'goalId' }, makeText((idx + 1) + "/" + count)),
        makeElement('span', { class: 'error' }, []),
        makeElement('span', { class: 'expr' }, makeText(goal))
    ]);
}
function createGoals(goals) {
    return makeElement('ul', { class: "goalsList" }, goals.map(function (g, i) { return createGoal(g, i, goals.length); }));
}
var StateModel = (function () {
    function StateModel() {
        this.statesE = document.getElementById('states');
        this.focusedState = 0;
    }
    StateModel.prototype.getCurrentStateE = function () {
        return this.statesE.getElementsByClassName(StateModel.focusedStateClass)[this.focusedState];
    };
    StateModel.prototype.getFocusStatesE = function () {
        return this.statesE.getElementsByClassName(StateModel.focusedStateClass);
    };
    StateModel.prototype.getGoalsE = function () {
        return this.statesE.getElementsByClassName(StateModel.goalNodeClass);
    };
    StateModel.prototype.getCurrentGoalE = function () {
        return this.getGoalsE()[0];
    };
    StateModel.prototype.currentHypsE = function () {
        this.statesE.getElementsByClassName(StateModel.focusedStateClass).item(this.focusedState);
    };
    StateModel.prototype.setMessage = function (message) {
        // document.getElementById('messages').innerHTML = message;
        setChildren(document.getElementById('messages'), makeText(message));
    };
    StateModel.prototype.setErrorMessage = function (message) {
        var errorsN = this.getCurrentGoalE().getElementsByClassName('error');
        if (errorsN.length > 0)
            setChildren(errorsN.item(0), makeText(message));
        // document.getElementById('messages').innerHTML = message;
        // setChildren(document.getElementById('messages'), [makeElement('span',{class:'error'},[makeText(message)])]);
    };
    StateModel.prototype.clearErrorMessage = function () {
        var errorsN = this.getCurrentGoalE().getElementsByClassName('error');
        if (errorsN.length > 0)
            setChildren(errorsN.item(0), []);
    };
    StateModel.prototype.updateState = function (state) {
        var _this = this;
        try {
            this.focusedState = 0;
            this.clearErrorMessage();
            // clearChildren(document.getElementById('messages'));
            if (state.error)
                this.setErrorMessage(state.error.message.toString());
            if (countAllGoals(state) == 0) {
                this.setMessage("No more subgoals.");
            }
            else if (state.goals) {
                if (state.goals.length > 0) {
                    setChildren(this.statesE, state.goals.map(function (hp, idx) {
                        return makeElement('div', { class: StateModel.focusedStateClass + (_this.focusedState === idx ? "" : " hidden") }, [createHypotheses(state.goals[idx].hypotheses),
                            createGoal(state.goals[idx].goal, idx, state.goals.length)
                        ]);
                    }));
                }
                else
                    this.setMessage("There are unfocused goals.");
            }
        }
        catch (err) {
            this.setMessage(err);
        }
    };
    StateModel.hypothesesNodeClass = 'hypotheses';
    StateModel.goalNodeClass = 'goal';
    StateModel.focusedStateClass = 'focusedState';
    return StateModel;
})();
