package main.visitor.nameAnalyzer;

import main.ast.node.Program;
import main.ast.node.declaration.ClassDeclaration;
import main.symbolTable.*;
import main.symbolTable.itemException.ItemNotFoundException;

import java.util.HashSet;
import java.util.Set;

public class SymbolTableClassParentLinker {

    public void findClassesParents( Program program )
    {
        Set<String> visitedClasses = new HashSet<>();
        for(ClassDeclaration classDeclaration: program.getClasses() )
        {
            linkClassWithItsParents( classDeclaration , visitedClasses );
        }
    }
    private void linkClassWithItsParents( ClassDeclaration classDeclaration , Set<String> visitedClasses )
    {
        SymbolTable currentSymTable, prevSymTable = null;
        ClassSymbolTableItem classItem;
        String name = classDeclaration.getName().getName();
        try {
            do {
                classItem = ((ClassSymbolTableItem) SymbolTable.root.getInCurrentScope(ClassSymbolTableItem.CLASS + name));
                currentSymTable = classItem.getClassSym();
                if (prevSymTable != null)
                    prevSymTable.setPreSymbolTable(currentSymTable);
                if (name != null && visitedClasses.contains(name))
                    break;
                visitedClasses.add(name);
                name = classItem.getParentName();
                prevSymTable = currentSymTable;
            } while (name != null);
        }
        catch( ItemNotFoundException itemNotFound )
        {
            System.out.println( "error occurred in linking parents" );
        }
    }
}
