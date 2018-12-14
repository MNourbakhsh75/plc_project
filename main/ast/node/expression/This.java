package main.ast.node.expression;

import main.visitor.Visitor;

public class This extends Expression {
    @Override
    public String toString() {
        return "This";
    }

    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
