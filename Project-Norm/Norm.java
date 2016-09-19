/*
this is a java program that takes Relationship, no. of functional dependencies and we need
scan all those functional dependencies line by line.
output will be guessing regarding candidate key , first normal for, second normal form and third
normal form was done.

created by Sai Suraj Reddy Doma 
 
*/


import java.util.*;


class Except extends RuntimeException
{
public String getMessage()               /*for some runtime exceptions*/
{
return "fd's must be in between the attributes or their combinations which are given in the relation.";
}
}

class Seperation        /*for converting user give fd's into 2d array*/ 
{
public String head="",tail="",rel="",s1="",s2="";

public Seperation(String str)     
{
rel=str;
}

public boolean scheck(String str)        /*for checking whether attributes in fd's are all in relation*/
{
int k=0;
for(int i=0;i<str.length();i++)         
{
s1=String.valueOf(str.charAt(i));
for(int j=0;j<rel.length();j++)
{
s2=String.valueOf(rel.charAt(j));
if(s1.equals(s2))
{
k=1;
break;
}
}
if(k==0)
{
return false;
}
}
if(k==1)
{
return true;
}
else
{
return false;
}
}

public String getHead(String str)
{
String var="";
for(int i=0;i<str.length();i++)             /*to get head of fd*/
{
s1=String.valueOf(str.charAt(i));
if(s1.equals("-"))
{
return var;
}
if(scheck(s1))
{
var=var.concat(s1);
}
else
{
Except e=new Except();
throw e;
}
}
return var;
}

public String getTail(String str)         /*to get tail of fd*/
{
String var="";
int flag=0;
for(int i=0;i<str.length();i++)
{
s1=String.valueOf(str.charAt(i));
if(s1.equals(">"))
{
flag=1;
continue;
}
if(flag==0)
{
continue;
}
else
{
if(scheck(s1))
{
var=var.concat(s1);
}
else
{
Except e=new Except();
throw e;
}
}
}
return var;
}

}


class Candidatekey        /*to find candidate keys*/
{
String[][] fd=new String[20][2];
String[] keys=new String[30];
String[] sa1=new String[200];
String[] sa2=new String[200];
String[] combiarray=new String[200];
String rel="",s1="",s2="";
int n=0,noc=0,ai=0;

public Candidatekey(String[][] f,String str,int n1)
{
fd=f;
rel=str;
n=n1;
}

public boolean checker(String ms,String ss)      /*checks whether ss is present in ms*/
{
int k=0;
for(int i=0;i<ss.length();i++)
{
s1=String.valueOf(ss.charAt(i));
for(int j=0;j<ms.length();j++)
{
s2=String.valueOf(ms.charAt(j));
if(s1.equals(s2))
{
k=1;
break;
}
else
{
k=0;
}
}
if(k==0)
{
return false;
}
}
if(k==1)
{
return true;
}
else
{
return false;
}
}

public String filter(String str)         /*filters str from repetition*/
{
String var="";
for(int i=0;i<rel.length();i++)
{
s1=String.valueOf(rel.charAt(i));
for(int j=0;j<str.length();j++)
{
s2=String.valueOf(str.charAt(j));
if(s1.equals(s2))
{
var=var.concat(s1);
break;
}
}
}
return var;
}

public String closure(String str)       /*finds closure of str*/
{
String closer="";
closer=closer.concat(str);
for(int i=0;i<n;i++)
{
for(int j=0;j<n;j++)
{
if(checker(closer,fd[j][0]))
{
closer=closer.concat(fd[j][1]);
}
}
}
closer=filter(closer);
return closer;
}

public boolean checker(String str)         /*checks whether all attributes are present in str*/
{
int k=0;
for(int i=0;i<rel.length();i++)
{
s1=String.valueOf(rel.charAt(i));
for(int j=0;j<str.length();j++)
{
s2=String.valueOf(str.charAt(j));
if(s1.equals(s2))
{
k=1;
break;
}
else
{
k=0;
}
}
if(k==0)
{
return false;
}
}
if(k==1)
{
return true;
}
else
{
return false;
}
}

public String seperate()         /*this find's the attributethat are not present on the left side of all fd's*/
{
int i=0,j=0,k=0;
String str="";
for(i=0;i<rel.length();i++)
{
s1=String.valueOf(rel.charAt(i));
for(j=0;j<n;j++)
{
for(k=0;k<fd[j][1].length();k++)
{
s2=String.valueOf(fd[j][1].charAt(k));
if(s1.equals(s2))
{
break;
}
}
if(k!=fd[j][1].length())
{
break;
}
}
if(j==n)
{
str=str.concat(s1);
}
}
return str;
}

public void filterall()     /*this filters keys from any repetition*/
{
for(int i=0;i<noc;i++)
{
keys[i]=filter(keys[i]);
}
for(int i=0;i<noc;i++)
{
for(int j=i+1;j<noc;j++)
{
if(keys[i].equals(keys[j]))
{
if(j==(noc-1))
{
keys[j]=null;
noc--;
}
else
{
keys[j]=keys[noc-1];
keys[noc-1]=null;
noc--;
}
}
}
}
}

public void addFd()       /*this add's left attribute that is not present on left side of every fd to every fd*/
{
//pseudotransitive();
String str=seperate();
if(!str.equals(""))
{
String var="";
for(int i=0;i<n;i++)
{
if(!checker(fd[i][0],str))
{
var=var.concat(fd[i][0]);
var=var.concat(str);
var=filter(var);
fd[i][0]=var;
var="";
var=var.concat(fd[i][1]);
var=var.concat(str);
var=filter(var);
fd[i][1]=var;
var="";
}
}
}
//pseudotransitive();
//getKeys();
//filterall();
}

public void pseudotransitive()        /*this add's new fd's based on the axiom pseudo transitive rule*/
{
int i=0,j=0;
String str="";
for(i=0;i<n;i++)
{
for(j=0;j<n;j++)
{
if(i==j)
{
continue;
}
if(fd[j][0].startsWith(fd[i][1]))
{
for(int k=fd[i][1].length();k<fd[j][0].length();k++)
{
s1=String.valueOf(fd[j][0].charAt(k));
str=str.concat(s1);
}
break;
}
}
if(!str.equals(""))
{
String var="";
var=var.concat(fd[i][0]);
var=var.concat(str);
fd[n][0]=var;
var="";
var=var.concat(fd[j][1]);
fd[n][1]=var;
n++;
str="";
}
}
}

public void getKeys()      /*coordinator that find's candidate keys*/
{
keys[0]="";
int k=0;
for(int i=0;i<n;i++)
{
s1=closure(fd[i][0]);
if(checker(s1))
{
keys[k++]=fd[i][0];
}
}
noc=k;
}

public void methodcoordinator()
{
getKeys();
if(keys[0].equals(""))
{
pseudotransitive();
getKeys();
filterall();
}
if(keys[0].equals(""))
{
addFd();
getKeys();
filterall();
}
if(keys[0].equals(""))
{
pseudotransitive();
getKeys();
filterall();
}
}

}


class Secondnormalform        /*to check for 2nf*/
{
String[][] fd=new String[20][2];
String[] keys=new String[30];
String[] voilater=new String[30];
String rel="",npa="",s1="",s2="";
int n=0,flag=0,noc=0;

public Secondnormalform(String[][] stda,String[] sa,String str,int n1,int noc1)    
{
fd=stda;
keys=sa;
rel=str;
n=n1;
noc=noc1;
}

public void nonprimeattributes()     /*find's non prime attributes*/
{
for(int i=0;i<rel.length();i++)
{
s1=String.valueOf(rel.charAt(i));
int var=0;
for(int j=0;j<noc;j++)
{
for(int k=0;k<keys[j].length();k++)
{
s2=String.valueOf(keys[j].charAt(k));
if(s1.equals(s2))
{
var=1;
break;
}
}
if(var==1)
{
break;
}
}
if(var==0)
{
npa=npa.concat(s1);
}
}
}

public boolean searchforanysubsets(String str,String attribute,int index)
{
int var=1;
for(int i=0;i<n;i++)
{
if(i==index)
{
continue;
}
Candidatekey ck=new Candidatekey(fd,rel,n);
if(ck.checker(str,fd[i][0]))
{
if(ck.checker(fd[i][1],attribute))
{
var=0;
return false;
}
else
{
var=1;
}
}
}
if(var==1)
{
return true;
}
else
{
return false;
}
}

public boolean fullyfuctionaldependency()       
{
int var=0;
for(int k=0;k<npa.length();k++)
{
s1=String.valueOf(npa.charAt(k));
for(int i=0;i<noc;i++)
{
for(int j=0;j<n;j++)
{
if(fd[j][0].equals(keys[i]))
{
Candidatekey ck=new Candidatekey(fd,rel,n);
if(ck.checker(fd[j][1],s1))
{
if(searchforanysubsets(fd[j][0],s1,j))
{
var=1;
}
else
{
var=0;
return false;
}
}
else
{
var=0;
return false;
}
}
}
}
}
if(var==1)
{
return true;
}
else
{
return false;
}
}

public void checkerfor2nf()
{
nonprimeattributes();
if(fullyfuctionaldependency())
{
flag=1;
System.out.println("The given relation is in 2nf");
}
else
{
System.out.println("The given relation is not in 2nf");
}
}

}



class Thirdnormalform
{
String[][] fd=new String[20][2];
String[] keys=new String[30];
String[] voilater=new String[30];
String rel="",npa="",s1="",s2="";
int n=0,flag=0,noc=0,flagof2nf=0;

public Thirdnormalform(String[][] stda,String[] sa,String str,String afnpa,int n1,int noc1,int f2nf)
{
fd=stda;
keys=sa;
rel=str;
npa=afnpa;
n=n1;
noc=noc1;
flagof2nf=f2nf;
}

public boolean transitivedependency()
{
for(int i=0;i<npa.length();i++)
{
s1=String.valueOf(npa.charAt(i));
for(int j=0;j<n;j++)
{
if(s1.equals(fd[j][0]))
{
for(int k=0;k<npa.length();k++)
{
if(i==k)
{
continue;
}
s2=String.valueOf(npa.charAt(k));
if(s2.equals(fd[j][1]))
{
return true;
}
}
}
}
}
return false;
}

public void checkerfor3nf()
{
if(flagof2nf==1)
{
if(!transitivedependency())
{
flag=1;
System.out.println("The given relation is in 3nf");
}
else
{
System.out.println("The given relation is not in 3nf");
}
}
else
{
System.out.println("The given relation is not in 3nf");
}
}

}



class Norm
{
     public static String method1(String s)
     {
         String s1="";
         for(int i=0;i<s.length();i++)
         {
             String s3="R";
             String s2;
             s2=String.valueOf(s.charAt(i));
             if(s3.equals(s2))
             {
                 continue;
             }
             s3="(";
             if(s3.equals(s2))
             {
                 continue;
             }
             s3=")";
             if(s3.equals(s2))
             {
                 continue;
             }
             s3=",";
             if(s3.equals(s2))
             {
                 continue;
             }
             s1=s1.concat(s2);
         }
         return s1;
     }


     public static void main(String[] args)
     {
        try{
            Scanner s=new Scanner(System.in);
            String relation=s.nextLine();
            System.out.println(relation);
            relation=method1(relation);
            System.out.println(relation);
            System.out.println("how many functional dependencies does this relation have?");
            int n=s.nextInt();
            Seperation sep=new Seperation(relation);
/*if(sep.scheck("B"))
{
System.out.println("yes");
}
String sn=sep.getHead("B->B");
System.out.println(sn);
sn=sep.getTail("A->BC");
System.out.println(sn);*/
            String var="";
            String[][] fd=new String[20][2];
            for(int i=0;i<n;i++)
            {
                System.out.println("enter the "+(i+1)+" functional dependency");
                var=s.next();
                fd[i][0]=sep.getHead(var);
                fd[i][1]=sep.getTail(var);
            }
/*for(int i=0;i<n;i++)
{
System.out.println(fd[i][0]+"      "+fd[i][1]);
}*/
            Candidatekey ck=new Candidatekey(fd,relation,n);
/*if(ck.checker("ABC","AC"))
{
System.out.println("yes");
}*/
/*String sn=ck.closure("C");
System.out.println(sn);
if(ck.checker("CD"))
{
System.out.println("yes");
}*/
//ck.getKeys();
/*sn=ck.seperate();
System.out.println(sn);*/
//ck.pseudotransitive();
//System.out.println("-------------------");
//ck.addFd();
ck.methodcoordinator();
//System.out.println("-------------------");
/*for(int i=0;i<ck.n;i++)
{
System.out.println(ck.fd[i][0]+"    "+ck.fd[i][1]);
}*/
           for(int i=0;i<ck.noc;i++)
           {
               System.out.print(ck.keys[i]+"  ");
           }
           System.out.println(" are the candidate keys");
           System.out.println("The given relation is in 1nf");
           Secondnormalform snf=new Secondnormalform(ck.fd,ck.keys,relation,ck.n,ck.noc);
/*snf.nonprimeattributes();
System.out.println(snf.npa);
if(snf.fullyfuctionaldependency())
{
System.out.println("yes");
}*/
           snf.checkerfor2nf();
Thirdnormalform tnf=new Thirdnormalform(ck.fd,ck.keys,relation,snf.npa,ck.n,ck.noc,snf.flag);
/*if(tnf.transitivedependency())
{
System.out.println("yes");
}*/
tnf.checkerfor3nf();
/*if(snf.searchforanysubsets("AB","C",0))
{
System.out.println("yes");
}*/
        }
        catch(Exception ex)
        {
            System.out.println(ex);
        }
    }

}