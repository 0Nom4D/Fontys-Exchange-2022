import 'package:flutter/material.dart';
import 'package:provider/provider.dart';

import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/widgets/picture_overlay.dart';
import 'package:psv_fan_experience/src/widgets/comment_modal.dart';
import 'package:psv_fan_experience/src/widgets/action_button.dart';
import 'package:psv_fan_experience/src/models/submission.dart';
import 'package:psv_fan_experience/src/models/user.dart';

class SubmissionPost extends StatefulWidget {
  const SubmissionPost({
    Key? key,
    required this.submission
  }) : super(key: key);

  final Submission submission;

  @override
  SubmissionPostState createState() => SubmissionPostState();
}

class SubmissionPostState extends State<SubmissionPost> {
  @override
  Widget build(BuildContext context) {
    return Consumer<SubmissionProvider>(
      builder: (context, provider, _) => Padding(
      padding: const EdgeInsets.all(15.0),
      child: Container(
        decoration: BoxDecoration(
          color: Theme.of(context).colorScheme.primary,
          borderRadius: BorderRadius.circular(20),
          boxShadow: [
            BoxShadow(
              color: Colors.black.withOpacity(0.2),
              spreadRadius: 1,
              blurRadius: 5,
              offset: const Offset(0, 3),
            ),
          ],
        ),
        child: Card(
          color: Colors.transparent,
          elevation: 0,
          shape: RoundedRectangleBorder(
            borderRadius: BorderRadius.circular(20),
          ),
          child: IntrinsicHeight(
            child: Column(
              children: [
                PictureOverlay(
                  userAvatar: User.placeholderUser.userProfilePicture,
                  username: User.placeholderUser.username,
                  imageAsset: widget.submission.picture,
                  competitionName: widget.submission.competition,
                  isFromAssets: widget.submission.isFromAsset,
                ),
                Row(
                  mainAxisAlignment: MainAxisAlignment.center,
                  crossAxisAlignment: CrossAxisAlignment.center,
                  children: [
                    ActionButton(
                      submission: provider.getSubmission(widget.submission),
                      showStat: true,
                      icon: Icon(Icons.favorite_outline, color: Theme.of(context).colorScheme.background),
                      accentIcon: Icon(Icons.favorite, color: Theme.of(context).colorScheme.primary),
                      callback: () {
                        provider.getSubmission(widget.submission).isLikedByUser
                          ? provider.unlikeSubmission(widget.submission)
                          : provider.likeSubmission(widget.submission);
                      }
                    ),
                    SizedBox(width: MediaQuery.of(context).size.width * .01),
                    ActionButton(
                      submission: provider.getSubmission(widget.submission),
                      showStat: false,
                      icon: Icon(Icons.comment, color: Theme.of(context).colorScheme.background),
                      callback: () => showBottomSheet(
                        context: context,
                        builder: (context) => CommentModal(
                          submission: widget.submission
                        )
                      )
                    ),
                    SizedBox(width: MediaQuery.of(context).size.width * .28),
                    IconButton(
                      icon: const Icon(
                        Icons.more_horiz_outlined,
                        color: Color(0xffffffff),
                      ),
                      iconSize: 50,
                      onPressed: () {},
                    ),
                  ],
                ),
              ],
            ),
          ),
        ),
      ),
    ));
  }
}
