import 'package:provider/provider.dart';
import 'package:flutter/material.dart';

import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/widgets/background_container.dart';
import 'package:psv_fan_experience/src/widgets/submission_post.dart';
import 'package:psv_fan_experience/src/widgets/psv_appbar.dart';
import 'package:psv_fan_experience/src/widgets/drawer.dart';

class SubmissionScreen extends StatelessWidget {
  const SubmissionScreen({super.key, this.selectedCompetition = ""});

  final String selectedCompetition;

  @override
  Widget build(BuildContext context) {
    return Consumer<SubmissionProvider>(
      builder: (context, provider, _) => Scaffold(
        endDrawerEnableOpenDragGesture: false,
        appBar: PSVAppbar(title: selectedCompetition == "" ? "TRENDING" : selectedCompetition),
        endDrawer: const PSVDrawer(),
        body: Background(
          child: Center(
            child: SizedBox(
              child: selectedCompetition == ""
              ? ListView.separated(
                itemBuilder: (context, index) => SubmissionPost(submission: provider.submissions[index]),
                separatorBuilder: (context, index) => const SizedBox(height: 2),
                itemCount: provider.submissions.length
              )
              : ListView.separated(
                itemBuilder: (context, index) => SubmissionPost(submission: provider.submissions.where((element) => element.competition == selectedCompetition).toList()[index]),
                separatorBuilder: (context, index) => const SizedBox(height: 2),
                itemCount: provider.submissions.where((element) => element.competition == selectedCompetition).length
              ),
            ),
          ),
        )
      ),
    );
  }
}