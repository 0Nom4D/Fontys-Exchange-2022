import 'dart:io';
import 'package:camera/camera.dart';
import 'package:flutter/material.dart';
import 'package:go_router/go_router.dart';
import 'package:provider/provider.dart';
import 'package:psv_fan_experience/src/models/submission.dart';
import 'package:psv_fan_experience/src/models/user.dart';

import 'package:psv_fan_experience/src/widgets/competition_selection_modal.dart';
import 'package:psv_fan_experience/src/widgets/parallelogram_trapezoid.dart';
import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/widgets/background_container.dart';
import 'package:psv_fan_experience/src/widgets/psv_appbar.dart';
import 'package:psv_fan_experience/src/widgets/drawer.dart';

class SubmissionUploadPage extends StatefulWidget {
  const SubmissionUploadPage(this.uploadPicture, {Key? key}) : super(key: key);

  final XFile uploadPicture;

  @override
  SubmissionUploadPageState createState() => SubmissionUploadPageState();
}

class SubmissionUploadPageState extends State<SubmissionUploadPage> {
  final TextEditingController controller = TextEditingController();
  String selectedCompetition = "";

  @override
  void dispose() {
    controller.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    SubmissionProvider provider = Provider.of<SubmissionProvider>(context);

    return Scaffold(
      endDrawerEnableOpenDragGesture: false,
      appBar: const PSVAppbar(title: 'SUBMISSION UPLOAD'),
      endDrawer: const PSVDrawer(),
      body: SizedBox(
        height: MediaQuery.of(context).size.height,
        child: Background(
          child: SingleChildScrollView(
            child: Padding(
              padding: const EdgeInsets.all(8.0),
              child: Center(
                child: Column(
                  crossAxisAlignment: CrossAxisAlignment.center,
                  children: [
                    Image.file(
                      File(widget.uploadPicture.path),
                      fit: BoxFit.cover,
                      width: MediaQuery.of(context).size.width * .9,
                      height: MediaQuery.of(context).size.height * .5
                    ),
                    SizedBox(height: MediaQuery.of(context).size.height * .025),
                    GestureDetector(
                      onTap: () async {
                        String? chosenCodeExt = await showModalBottomSheet<String?>(
                          context: context,
                          shape: const RoundedRectangleBorder(
                            borderRadius: BorderRadius.only(
                              topLeft: Radius.circular(10.0),
                              topRight: Radius.circular(10.0),
                            ),
                          ),
                          backgroundColor: Colors.white,
                          builder: (context) => const CompetitionSelectionModal()
                        );
                        if (chosenCodeExt == null) {
                          return;
                        }
                        setState(() {
                          selectedCompetition = chosenCodeExt;
                        });
                      },
                      child: SizedBox(
                        width: MediaQuery.of(context).size.width * .7,
                        child: ClipPath(
                          clipper: TrapezoidClipper(),
                          child: DecoratedBox(
                            decoration: BoxDecoration(
                              color: Theme.of(context).colorScheme.secondary
                            ),
                            child: Row(
                              mainAxisAlignment: MainAxisAlignment.spaceEvenly,
                              crossAxisAlignment: CrossAxisAlignment.center,
                              children: [
                                Text(
                                  "COMPETITIONS",
                                  style: TextStyle(
                                    color: Theme.of(context).colorScheme.tertiary,
                                    fontSize: 16
                                  ),
                                ),
                                Icon(
                                  Icons.chevron_right,
                                  color: Theme.of(context).colorScheme.tertiary
                                )
                              ],
                            )
                          ),
                        ),
                      ),
                    ),
                    if (selectedCompetition != "")
                      ...[
                        SizedBox(height: MediaQuery
                          .of(context)
                          .size
                          .height * .005),
                        Center(
                          child: Text(
                            "You selected the '$selectedCompetition' competition.",
                            style: TextStyle(
                              color: Theme
                                .of(context)
                                .colorScheme
                                .secondary
                            )
                          )
                        ),
                      ],
                    SizedBox(height: MediaQuery.of(context).size.height * .025),
                    SizedBox(
                      width: MediaQuery.of(context).size.width * .9,
                      child: TextField(
                        controller: controller,
                        keyboardType: TextInputType.multiline,
                        maxLines: null,
                        decoration: InputDecoration(
                          filled: true,
                          fillColor: Theme.of(context).colorScheme.background,
                          border: const OutlineInputBorder(
                            borderRadius: BorderRadius.all(Radius.circular(8.0))
                          ),
                          label: const Text('Write a caption')
                        ),
                      ),
                    ),
                    SizedBox(height: MediaQuery.of(context).size.height * .025),
                    SizedBox(
                      width: MediaQuery.of(context).size.width * .6,
                      child: ElevatedButton(
                        onPressed: selectedCompetition == "" ? null : () {
                          provider.createSubmission(Submission(
                            picture: widget.uploadPicture.path,
                            isFromAsset: false,
                            caption: controller.text,
                            username: User.placeholderUser.username,
                            competition: selectedCompetition
                          ));
                          ScaffoldMessenger.of(context).showSnackBar(
                            const SnackBar(content: Text("Your submission has been created!"))
                          );

                          Future.delayed(const Duration(seconds: 2), () {
                            context.go('/');
                          });
                        },
                        style: ElevatedButton.styleFrom(
                          backgroundColor: Theme.of(context).colorScheme.primary
                        ),
                        child: Text(
                          'UPLOAD',
                          style: TextStyle(
                            color: Theme.of(context).colorScheme.tertiary,
                            fontSize: 16
                          ),
                        )
                      ),
                    )
                  ],
                )
              ),
            ),
          ),
        ),
      ),
    );
  }
}