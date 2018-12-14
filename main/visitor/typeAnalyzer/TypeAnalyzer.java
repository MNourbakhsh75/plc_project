package main.visitor.typeAnalyzer;

import main.ast.node.Node;
import main.ast.node.Program;
import main.ast.node.declaration.ClassDeclaration;
import main.ast.node.declaration.MainMethodDeclaration;
import main.ast.node.declaration.MethodDeclaration;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.expression.*;
import main.ast.node.expression.Value.BooleanValue;
import main.ast.node.expression.Value.IntValue;
import main.ast.node.expression.Value.StringValue;
import main.ast.node.statement.*;
import main.ast.Type.*;
import main.ast.Type.ArrayType.*;
import main.ast.Type.PrimitiveType.*;
import main.ast.Type.UserDefinedType.*;
import main.symbolTable.ClassSymbolTableItem;
import main.symbolTable.itemException.ItemNotFoundException;
import main.symbolTable.*;
import main.symbolTable.SymbolTable;
import main.symbolTable.SymbolTableMethodItem;
import main.symbolTable.symbolTableVariable.SymbolTableFieldVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableLocalVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableVariableItemBase;
import main.visitor.VisitorImpl;
import main.visitor.nameAnalyzer.*;
import java.util.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class TypeAnalyzer extends VisitorImpl {
    private SymbolTableConstructor symConstructor;
    private TraverseState traverseState;
    private SymbolTableClassParentLinker symTableClassLinker;
    private ArrayList<String> nameErrors;
    private int lastIndexOfVariable;

    public TypeAnalyzer() {
        symConstructor = new SymbolTableConstructor();
        symTableClassLinker = new SymbolTableClassParentLinker();
        nameErrors = new ArrayList<>();
        lastIndexOfVariable = 0;
        setState(TraverseState.symbolTableConstruction);
    }

    public int numOfErrors() {
        return nameErrors.size();
    }

    private void switchState() {
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            setState(TraverseState.redefinitionAndArrayErrorCatching);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())
                && nameErrors.size() != 0)
            setState(TraverseState.PrintError);
        else
            setState(TraverseState.Exit);
    }

    private void setState(TraverseState traverseState) {
        this.traverseState = traverseState;
    }

    private void checkForPropertyRedefinition(ClassDeclaration classDeclaration) {
        String name = classDeclaration.getName().getName();
        if (name.indexOf('$') != -1)
            nameErrors.add("Line:" + classDeclaration.getName().getLineNum() + ":Redefinition of class "
                    + name.substring(name.indexOf('$') + 1));
        try {
            ClassSymbolTableItem classItem = (ClassSymbolTableItem) SymbolTable.root
                    .getInCurrentScope(ClassSymbolTableItem.CLASS + name);
            SymbolTable next = classItem.getClassSym();
            SymbolTable.push(next);
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("there is an error in pushing class symbol table");
        }
    }

    private void checkForPropertyRedefinitionInParentScopes(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        Set<SymbolTable> visitedSymbolTables = new HashSet<>();
        String variableKey = SymbolTableVariableItemBase.VARIABLE + name;
        SymbolTable current = SymbolTable.top.getPreSymbolTable();
        visitedSymbolTables.add(SymbolTable.top);
        while (current != null && !visitedSymbolTables.contains(current)) {
            visitedSymbolTables.add(current);
            try {
                current.getInCurrentScope(variableKey);
                SymbolTableVariableItemBase variable = (SymbolTableVariableItemBase) SymbolTable.top
                        .getInCurrentScope(variableKey);
                variable.setName("$" + variable.getName());
                SymbolTable.top.updateItemInCurrentScope(variableKey, variable);
                nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() + ":Redefinition of variable "
                        + name.substring(name.indexOf('$') + 1));
                return;
            } catch (ItemNotFoundException itemNotFound) {
                current = current.getPreSymbolTable();
            }
        }
    }

    private void checkForPropertyRedefinition(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        if (name.indexOf('$') != -1) {
            nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() + ":Redefinition of variable "
                    + name.substring(name.indexOf('$') + 1));
            return;
        }
        try {
            SymbolTableVariableItemBase varItem = (SymbolTableVariableItemBase) SymbolTable.top
                    .getInCurrentScope(SymbolTableVariableItemBase.VARIABLE + name);
            varItem.setIndex(lastIndexOfVariable++);
            SymbolTable.top.updateItemInCurrentScope(SymbolTableVariableItemBase.VARIABLE + name, varItem);
            if (varItem instanceof SymbolTableFieldVariableItem)
                checkForPropertyRedefinitionInParentScopes(varDeclaration);
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("not important");
        }
    }

    private void checkForPropertyRedefinitionInParentScope(MethodDeclaration methodDeclaration) {
        String name = methodDeclaration.getName().getName();
        String methodKey = SymbolTableMethodItem.METHOD + name;
        SymbolTable current = SymbolTable.top.getPreSymbolTable();
        Set<SymbolTable> visitedSymbolTables = new HashSet<>();
        visitedSymbolTables.add(SymbolTable.top);
        while (current != null && !visitedSymbolTables.contains(current)) {
            visitedSymbolTables.add(current);
            try {
                current.getInCurrentScope(methodKey);
                SymbolTableMethodItem method = (SymbolTableMethodItem) SymbolTable.top.getInCurrentScope(methodKey);
                method.setName("$" + method.getName());
                SymbolTable.top.updateItemInCurrentScope(methodKey, method);
                nameErrors.add("Line:" + methodDeclaration.getName().getLineNum() + ":Redefinition of method "
                        + name.substring(name.indexOf('$') + 1));
                return;
            } catch (ItemNotFoundException itemNotFound) {
                current = current.getPreSymbolTable();
            }
        }
    }

    private void checkForPropertyRedefinition(MethodDeclaration methodDeclaration) {
        String name = methodDeclaration.getName().getName();
        SymbolTable next = null;
        String methodKey = SymbolTableMethodItem.METHOD + name;
        try {
            next = ((SymbolTableMethodItem) SymbolTable.top.getInCurrentScope(methodKey)).getMethodSymbolTable();
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("an error occurred in pushing method symbol table");
            return;
        }
        if (name.indexOf('$') != -1) {
            nameErrors.add("Line:" + methodDeclaration.getName().getLineNum() + ":Redefinition of method "
                    + name.substring(name.indexOf('$') + 1));
            SymbolTable.push(next);
            return;
        }
        checkForPropertyRedefinitionInParentScope(methodDeclaration);
        SymbolTable.push(next);
    }
    
    private void checkForUndefinedVar(MethodDeclaration methodDeclaration) {
        String name = methodDeclaration.getName().getName();
        SymbolTable next = null;
        String methodKey = SymbolTableMethodItem.METHOD + name;
        try {
            next = ((SymbolTableMethodItem) SymbolTable.top.getInCurrentScope(methodKey)).getMethodSymbolTable();
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("an error occurred in pushing method symbol table");
            return;
        }
        if (name.indexOf('$') != -1) {
            nameErrors.add("Line:" + methodDeclaration.getName().getLineNum() + ":Redefinition of method "
                    + name.substring(name.indexOf('$') + 1));
            SymbolTable.push(next);
            return;
        }
        checkForPropertyRedefinitionInParentScope(methodDeclaration);
        SymbolTable.push(next);
    }
    
    private void checkForUndefinedType(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        Type type = varDeclaration.getType();
        boolean checked = false;
        if( !((type instanceof ArrayType) || (type instanceof IntType) || (type instanceof BooleanType) || (type instanceof StringType)))
        {
            if ((type instanceof UserDefinedType)){
                HashMap <String, SymbolTableItem> hm = SymbolTable.root.getSymItems();
                for (SymbolTableItem value : hm.values()) {
                    ClassSymbolTableItem classItem = (ClassSymbolTableItem) value;
                    String className = classItem.getClassDeclaration().getName().getName();
                    if(className.equals(type.toString())){
                        checked = true;
                    }
                }
            }
            if (!checked){
                // if (name.indexOf('$') != -1) {
                    nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() +
                    ":Undefined Type For Variable "
                    + name.substring(name.indexOf('$') + 1));
                    return;
                // }
            }
        }        
    }

    @Override
    public void visit(Node node) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(Program program) {
        // TODO: implement appropriate visit functionality
        while (!traverseState.toString().equals(TraverseState.Exit.toString())) {
            // System.out.println("traverseState : " + traverseState.toString());
            if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
                symConstructor.constructProgramSym();
            else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
                symTableClassLinker.findClassesParents(program);
            else if (traverseState.name().equals(TraverseState.PrintError.toString())) {
                for (String error : nameErrors)
                    System.out.println(error);
                return;
            }
            this.visit(program.getMainClass());
            for (ClassDeclaration classDeclaration : program.getClasses())
                this.visit(classDeclaration);
            switchState();
        }
    }

    @Override
    public void visit(ClassDeclaration classDeclaration) {
        // TODO: implement appropriate visit functionality
        if (classDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            symConstructor.construct(classDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            checkForPropertyRedefinition(classDeclaration);
        visitExpr(classDeclaration.getName());
        visitExpr(classDeclaration.getParentName());
        for (VarDeclaration varDeclaration : classDeclaration.getVarDeclarations())
            this.visit(varDeclaration);
        for (MethodDeclaration methodDeclaration : classDeclaration.getMethodDeclarations())
            this.visit(methodDeclaration);
        SymbolTable.pop();
    }

    @Override
    public void visit(MethodDeclaration methodDeclaration) {
        // TODO: implement appropriate visit functionality
        // System.out.println("hhh : " + SymbolTable.top);
        if (methodDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            symConstructor.construct(methodDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            checkForPropertyRedefinition(methodDeclaration);
        for (VarDeclaration argDeclaration : methodDeclaration.getArgs())
            visit(argDeclaration);
        for (VarDeclaration localVariable : methodDeclaration.getLocalVars()) {
            // System.out.println("localVariable : " + localVariable.getIdentifier().getName());
            this.visit(localVariable);
        }
        for (Statement statement : methodDeclaration.getBody())
            visitStatement(statement);
        visitExpr(methodDeclaration.getReturnValue());
        SymbolTable.pop();
    }

    @Override
    public void visit(MainMethodDeclaration mainMethodDeclaration) {
        // TODO: implement appropriate visit functionality
        if (mainMethodDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            visit((MethodDeclaration) mainMethodDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            visit((MethodDeclaration) mainMethodDeclaration);
        for (Statement statement : mainMethodDeclaration.getBody())
            visitStatement(statement);
        visitExpr(mainMethodDeclaration.getReturnValue());
    }

    @Override
    public void visit(VarDeclaration varDeclaration) {
        // TODO: implement appropriate visit functionality
        if (varDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
            checkForPropertyRedefinition(varDeclaration);
            checkForUndefinedType(varDeclaration);
        }
        visitExpr(varDeclaration.getIdentifier());
    }

    @Override
    public void visit(ArrayCall arrayCall) {
        // TODO: implement appropriate visit functionality
        if (arrayCall == null)
            return;
        try {
            visitExpr(arrayCall.getInstance());
            visitExpr(arrayCall.getIndex());
        } catch (NullPointerException npe) {
            System.out.println("instance or index is null");
        }

    }

    @Override
    public void visit(BinaryExpression binaryExpression) {
        // TODO: implement appropriate visit functionality
        if (binaryExpression == null)
            return;
        Expression lOperand = binaryExpression.getLeft();
        Expression rOperand = binaryExpression.getRight();
        try {
            visitExpr(lOperand);
            visitExpr(rOperand);
        } catch (NullPointerException npe) {
            System.out.println("one of operands is null, there is a syntax error");
        }
    }

    @Override
    public void visit(Identifier identifier) {
        // TODO: implement appropriate visit functionality

    }

    @Override
    public void visit(Length length) {
        // TODO: implement appropriate visit functionality
        if (length == null)
            return;
        visitExpr(length.getExpression());
    }

    @Override
    public void visit(MethodCall methodCall) {
        if (methodCall == null)
            return;
        try {
            visitExpr(methodCall.getInstance());
            visitExpr(methodCall.getMethodName());
            for (Expression argument : methodCall.getArgs())
                visitExpr(argument);
        } catch (NullPointerException npe) {
            System.out.println("syntax error occurred");
        }
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(NewArray newArray) {
        // TODO: implement appropriate visit functionality
        if (newArray == null)
            return;
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            if (newArray.getExpression() instanceof IntValue
                    && ((IntValue) newArray.getExpression()).getConstant() <= 0) {
                nameErrors.add("Line:" + newArray.getExpression().getLineNum()
                        + ":Array length should not be zero or negative");
                ((IntValue) newArray.getExpression()).setConstant(0);
            }
        visitExpr(newArray.getExpression());
    }

    @Override
    public void visit(NewClass newClass) {
        // TODO: implement appropriate visit functionality
        if (newClass == null)
            return;
        visitExpr(newClass.getClassName());
    }

    @Override
    public void visit(This instance) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(UnaryExpression unaryExpression) {
        // TODO: implement appropriate visit functionality
        if (unaryExpression == null)
            return;
        try {
            visitExpr(unaryExpression.getValue());
        } catch (NullPointerException npe) {
            System.out.println("unary value is null");
        }
    }

    @Override
    public void visit(BooleanValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(IntValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(StringValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(Assign assign) {
        // TODO: implement appropriate visit functionality
        if (assign == null)
            return;
        try {
            Expression lExpr = assign.getlValue();
            visitExpr(lExpr);
            Expression rValExpr = assign.getrValue();
            if (rValExpr != null)
                visitExpr(rValExpr);
        } catch (NullPointerException npe) {
            System.out.println("lvalue expression is null");
        }
    }

    @Override
    public void visit(Block block) {
        // TODO: implement appropriate visit functionality
        if (block == null)
            return;
        for (Statement blockStat : block.getBody())
            this.visitStatement(blockStat);
    }

    @Override
    public void visit(Conditional conditional) {
        // TODO: implement appropriate visit functionality
        if (conditional == null)
            return;
        visitExpr(conditional.getExpression());
        visitStatement(conditional.getConsequenceBody());
        visitStatement(conditional.getAlternativeBody());
    }

    @Override
    public void visit(While loop) {
        // TODO: implement appropriate visit functionality
        if (loop == null)
            return;
        visitExpr(loop.getCondition());
        visitStatement(loop.getBody());

    }

    @Override
    public void visit(Write write) {
        // TODO: implement appropriate visit functionality
        if (write == null)
            return;

        visitExpr(write.getArg());
    }
}
