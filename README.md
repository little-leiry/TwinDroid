# TwinDroid

This repo is the prototype implementation for our USENIX Security'23 paper. Please read it before running this project.

- Rui Li, [Wenrui Diao (✉️)](https://diaowenrui.github.io/), Shishuai Yang, Xiangyu Liu, Shanqing Guo, and Kehuan Zhang. Lost in Conversion: Exploit Data Structure Conversion with Attribute Loss to Break Android Systems. *The 32nd USENIX Security Symposium*, Anaheim, CA, USA. August 9-1, 2023. 

------

**TwinDroid** is a data flow analysis tool against the Android source code to detect the `Evil Twins` flaw. The `Evil Twins` flaw is a new category of flaws lying in the Android manifest processing procedures. Its fundamental cause is that the ill-considered data structure conversion procedure with attribute loss leads to system configuration inconsistency.

------

### Usage:

Default target Android version: `Android 11 & 12 `.

Input: the `DEX` files under the `/system/framework` directory extracted from the [Android images](https://developers.google.com/android/images).

Output: the `/logs/parsing` and `/logs/processing` directories, including:

- For *Stage 1 - Find Target Package Settings*: `target_settings.txt`, all identified target package settings' information.


- For *Stage 2 - Identify Suspicious Processing Methods*: `suspicious_methods.txt` and `suspicious_methods_final.txt`, all identified suspicious processing methods' information (original results & without false positives).


- Other analysis information that can help you understand the whole data flow analysis procedure and facilitate you to identify the `Evil Twins` flaw-related vulnerabilities, such as `analysis_data.txt`, `method_data.txt`, `element_data.txt`, `processing_method_data.txt`, etc.

------

### Running Environment Setup:

TwinDroid is `Java-style` and based on [`Soot`](https://soot-oss.github.io/soot/). Therefore, you should build a `Java` project and include `Soot` (e.g., through `Maven`) in your project.

------

#### Notes:

Adjust the package name of the `ParsingPackageUtils` module if the Android version to be analyzed is not 11 or 12.
