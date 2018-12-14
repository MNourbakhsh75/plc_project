package main.visitor.nameAnalyzer;

import main.compileError.CompileErrorException;

public class InheritanceCycleException extends CompileErrorException {
    private String name;
    private String parent;
    public InheritanceCycleException( String name , String parent )
    {
        this.name = name;
        this.parent = parent;
    }
    public String getName()
    {
        return name;
    }
    public String getParent()
    {
        return parent;
    }
}
