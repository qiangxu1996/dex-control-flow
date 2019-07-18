plugins {
    java
}

group = "edu.purdue"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    compile("org.smali:dexlib2:2.2.7")
    compile("ca.mcgill.sable:soot:3.3.0")
    testCompile("junit", "junit", "4.12")
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_11
}