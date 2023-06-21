import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'package:go_router/go_router.dart';

import 'package:app/src/widgets/category.dart';

class VideoAnalysisResult extends StatefulWidget {
  const VideoAnalysisResult({super.key});

  @override
  VideoAnalysisResultState createState() => VideoAnalysisResultState();
}

class VideoAnalysisResultState extends State<VideoAnalysisResult> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        leading: BackButton(
          color: Colors.white,
          onPressed: () => {
            HapticFeedback.lightImpact(),
            GoRouter.of(context).pop(),
          }
        ),
        title: const Text(
          "",
          style: TextStyle(
            color: Colors.black,
            fontWeight: FontWeight.bold,
            fontSize: 40,
          )
        ),
        backgroundColor: Colors.transparent,
      ),
      body: Padding(
        padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 15),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            const Text(
              "Post-Analysis",
              textAlign: TextAlign.start,
              style: TextStyle(
                color: Colors.white,
                fontSize: 40,
                fontWeight: FontWeight.bold
              ),
            ),
            const SizedBox(height: 15),
            Row(
              mainAxisAlignment: MainAxisAlignment.spaceEvenly,
              crossAxisAlignment: CrossAxisAlignment.center,
              children: const [
                AnalysisCategory(categoryTitle: "ATTEMPTS", description: "4"),
                AnalysisCategory(categoryTitle: "MISS", description: "2"),
                AnalysisCategory(categoryTitle: "SCORE", description: "2"),
              ],
            ),
            const SizedBox(height: 30),
            const Text(
              "Tracing Result:",
              textAlign: TextAlign.start,
              style: TextStyle(
                color: Colors.white,
                fontSize: 20,
                fontWeight: FontWeight.bold
              ),
            ),
            Padding(
              padding: const EdgeInsets.all(8.0),
              child: Align(
                alignment: Alignment.center,
                child: Image.asset("assets/post_analysis.png", fit: BoxFit.cover)
              ),
            )
          ],
        )
      )
    );
  }
}
