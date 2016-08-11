//
//  main.cpp
//  GG
//
//  Created by Dreamcastle on 2016/8/11.
//  Copyright © 2016年 Dreamcastle. All rights reserved.
//

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstring>
#include <cstdlib>

using namespace std;

string a1;
string a2;
string a3;
string a4;
string a5;

struct Vertex {
    long vertexID;
    int capacity;
} Vertex;

struct Edge {
    long srcID, destinID;
    int attr;
} Edge;

vector<struct Vertex> v;
vector<struct Edge> e;
vector<struct Edge> combination;

long sumOfWeight = 0;

void countWeight(vector<struct Edge> comb) {
    long tmp_max = 0;
    for(int i = 0; i<comb.size(); i++){
        tmp_max += comb[i].attr;
    }
    if(tmp_max > sumOfWeight){
        sumOfWeight = tmp_max;
        
        /*
        string boutputtext = string("./")+a1.c_str()+string("-")+a2.c_str()+string("-")+a3.c_str()+string("-")+a4.c_str()+string("-")+a5.c_str()+string("-boutput.txt");
        
        ofstream f;
        f.open(boutputtext.c_str(),ios_base::out);
        

        for(int i = 0; i<comb.size(); i++){
            f<< "Edge("<< comb[i].srcID<< ","<< comb[i].destinID<< ","<< comb[i].attr<<")"<<endl;
        }
        */
    }
}

bool checkEdge(vector<struct Edge> comb){
    vector<struct Vertex> check_v;
    check_v = v;
    for(int i = 0; i<comb.size(); i++){
        
        check_v[comb[i].srcID].capacity--;
        check_v[comb[i].destinID].capacity--;
        
        if(check_v[comb[i].srcID].capacity == -1 || check_v[comb[i].destinID].capacity == -1){
            return false;
        }
    }
    return true;
}

void go(int offset, int k) {
    if(checkEdge(combination) == false){
        return;
    }
    if (k == 0) {
        countWeight(combination);
        return;
    }
    for (int i = offset; i <= e.size() - k; ++i) {
        combination.push_back(e[i]);
        go(i+1, k-1);
        combination.pop_back();
    }
}

int main(int argc,char *argv[])
{
    string argv1(argv[1]);
    string argv2(argv[2]);
    string argv3(argv[3]);
    string argv4(argv[4]);
    string argv5(argv[5]);
    
    a1 = argv1;
    a2 = argv2;
    a3 = argv3;
    a4 = argv4;
    a5 = argv5;
    
    string edgetext = string("./")+argv1.c_str()+string("-")+argv2.c_str()+string("-")+argv3.c_str()+string("-")+argv4.c_str()+string("-")+argv5.c_str()+string("-edge.txt");
    string vertextext = string("./")+argv1.c_str()+string("-")+argv2.c_str()+string("-")+argv3.c_str()+string("-")+argv4.c_str()+string("-")+argv5.c_str()+string("-vertex.txt");
    string bresulttext = string("./")+argv1.c_str()+string("-")+argv2.c_str()+string("-")+argv3.c_str()+string("-")+argv4.c_str()+string("-")+argv5.c_str()+string("-bresult.txt");
    string poutput = string("./")+argv1.c_str()+string("-")+argv2.c_str()+string("-")+argv3.c_str()+string("-")+argv4.c_str()+string("-")+argv5.c_str()+string("-poutput.txt");
    string presult = string("./")+argv1.c_str()+string("-")+argv2.c_str()+string("-")+argv3.c_str()+string("-")+argv4.c_str()+string("-")+argv5.c_str()+string("-presult.txt");
    
    
    ofstream file;
    file.open(edgetext.c_str(),ios_base::out);
    file.close();
    file.open(vertextext.c_str(),ios_base::out);
    file.close();
    file.open(poutput.c_str(),ios_base::out);
    file.close();
    file.open(presult.c_str(),ios_base::out);
    file.close();
    
    int vertexNum = atoi(argv[1]);
    int maxCapacity = atoi(argv[2]);
    
    unsigned seed;
    seed = (unsigned)time(NULL);
    srand(seed);
    
    struct Vertex tmp;
    tmp.vertexID = 0;
    tmp.capacity = -1;
    v.push_back(tmp);
    
    file.open(vertextext.c_str(),ios_base::app);
    
    for(int i = 1; i <= vertexNum ; i++){
        
        tmp.vertexID = i;
        tmp.capacity = (rand() % maxCapacity) + 1;
        
        v.push_back(tmp);
        
        file << tmp.vertexID << " " << tmp.capacity << endl;
        
        
        //cout<< i <<" "<< v[i].capacity <<endl;
    }
    
    file.close();
    
    int maxWeight = atoi(argv[3]);
    int alpha = atoi(argv[4]);
    
    file.open(edgetext.c_str(),ios_base::app);
    
    for(int i = 1; i <= vertexNum; i++){
        for(int j = i; j <= vertexNum; j++){
            if(i == j) continue;
            else {
                if(rand() % alpha == 1){
                    
                    struct Edge tmp;
                    tmp.srcID = i;
                    tmp.destinID = j;
                    tmp.attr = (rand() % maxWeight) + 1;
                    
                    e.push_back(tmp);
                    
                    file << tmp.srcID << " " << tmp.destinID  << " " << tmp.attr << endl;
                    
                    
                }else{
                    continue;
                }
            }
        }
    }
    
    file.close();
    
    for(int i = 1; i <= e.size(); i++){
        go(0, i);
    }
    
    file.open(bresulttext.c_str(),ios::out);
    file << sumOfWeight << endl;
    file.close();
    
    return 0;
}
